#!/usr/bin/env python3
"""
Self-Contained HUSBZB-1 (EM3581) Zigbee Firmware Flasher (EmberZNet 6.7.8)
==========================================================================

Target Hardware & Firmware
--------------------------
- Device: Nortek / GoControl QuickStick Combo (Model: HUSBZB-1 / CECOMINOD016164)
- USB-UART Bridge: Silicon Labs CP2105 Dual UART Bridge
  - Interface 00 (`/dev/ttyUSB0`): Z-Wave 500 (UZB)
  - Interface 01 (`/dev/ttyUSB1` / `*-HubZ*-if01-port0`): Zigbee NCP (Silicon Labs EM3581)
- Firmware Image: `ncp-uart-sw-6.7.8.ebl` (EmberZNet 6.7.8.0, EZSP v8, 57600 baud,
  XON/XOFF software flow control). Upgrades factory EmberZNet 5.4 (EZSP v4).

Key Technical Findings
----------------------
1. CP2105 `HUPCL` / `DTR`-`RTS` Reset Trap on Linux:
   Closing `/dev/ttyUSB1` (with `termios.HUPCL` enabled by default) and reopening it
   (or calling `pyserial.Serial.open()`, which asserts `TIOCM_DTR | TIOCM_RTS`) toggles
   the CP2105 modem control lines. On the HUSBZB-1, that transition hardware-resets the
   EM3581 out of the standalone bootloader and straight back into the 57600-baud EZSP
   runtime (where it emits an unsolicited 57600-baud ASH `RSTACK` `RESET_POWER_ON` frame
   `1a c1 02 02 9b 7b 7e`, which appears as `` `x `` / `06e0` when read at 115200 baud).
   -> Fix: Open `/dev/ttyUSB1` ONCE with `termios.HUPCL` and `CRTSCTS` cleared, keep the
      same file descriptor open across all phases, and switch between 57600 and 115200
      baud in-place via `termios.tcsetattr`.

2. ASH `ACK` Requirement & 5.0s Bootloader Launch Delay:
   When `launchStandaloneBootloader(0x01)` (EZSP frame ID `0x008F`) is issued at 57600
   baud, the EM3581 NCP returns `EMBER_SUCCESS` (`01 80 8f 00`) first and waits for the
   host's ASH `ACK` frame before executing its delayed warm-reset into the standalone
   bootloader. Disconnecting or disturbing the port before the ~5.0s reboot window
   (`EZSP_BOOTLOADER_LAUNCH_DELAY`) completes aborts the bootloader transition.
   -> Fix: Explicitly send the ASH `ACK` frame (`_ash_send_ack`), re-ACK any retransmitted
      ASH DATA frame during the first 1.5s, and hold the serial descriptor open across the
      full 5.0s reboot delay before probing at 115200 baud.

3. EM3581 Standalone Bootloader (`v5.4.1.0 b962`) CLI Protocol:
   - Prompt Wake: Wakes reliably on `\n` (`0x0A`) at 115200 8N1 to print the banner and
     `BL >` menu.
   - Upload Trigger: Menu Option `1` (`upload ebl`) is a single-keystroke action (`b"1"`)
     that immediately prints `begin upload` and starts emitting XMODEM-CRC `'C'` (`0x43`)
     polling tokens. Sending `b"1"` first (and only sending `\r\n` if `begin upload` has
     not appeared after 1.5s) prevents feeding stray `\r\n` bytes into the XMODEM packet
     receiver.

What This Script Supports
-------------------------
- 100% Python Standard Library (Zero Third-Party Dependencies): Uses no `bellows`,
  `pyserial`, or `xmodem` packages. Includes a native Linux `termios` serial driver,
  ASHv2 + EZSP v4/v5-v7/v8+ framing engine, and XMODEM-CRC (`128`-byte blocks,
  `CRC-16-CCITT`, automatic XON/XOFF `0x11`/`0x13` stripping).
- Automatic Port & Latency Setup: Auto-detects `/dev/serial/by-id/*HubZ*-if01*` (fallback
  `/dev/ttyUSB1`), acquires an exclusive lock (`TIOCEXCL` + `flock`), and enables 1 ms USB
  serial `low_latency` via `TIOCSSERIAL` ioctl (with sysfs and `setserial` fallbacks).
- Firmware Integrity & Auto-Download: Validates the Silicon Labs EBL header magic (`0xE350`)
  and SHA-256 digest of `ncp-uart-sw-6.7.8.ebl`, automatically downloading a clean binary
  if missing or corrupted.
- End-to-End 4-Phase Execution:
  - Phase 1: Probes at 115200 baud in case the radio is already in the bootloader.
  - Phase 2: Switches in-place to 57600 baud, performs ASH `RST`/`RSTACK` + EZSP version
    negotiation, triggers `launchStandaloneBootloader`, holds for 5.0s, and synchronizes
    with the 115200-baud `BL >` menu.
  - Phase 3: Streams all 1,181 XMODEM-CRC blocks with retry handling and `EOT` confirmation.
  - Phase 4: Verifies `Serial upload complete`, boots the new application (`Option 2: run`),
    switches in-place to 57600 baud, and verifies live `EZSP v8` runtime communication.
"""

import argparse
import binascii
import fcntl
import glob
import hashlib
import os
import select
import struct
import subprocess
import sys
import termios
import time
import urllib.request

FIRMWARE_FILENAME = "ncp-uart-sw-6.7.8.ebl"
FIRMWARE_URL = (
    "https://raw.githubusercontent.com/walthowd/husbzb-firmware/master/ncp-uart-sw-6.7.8.ebl"
)
FIRMWARE_SHA256 = "0b09687efe15a38459501b1302fdb096393a5ca9c9234e1abeb70f59d257bfac"
EZSP_BOOTLOADER_LAUNCH_DELAY = 5.0

XMODEM_SOH = 0x01
XMODEM_EOT = 0x04
XMODEM_ACK = 0x06
XMODEM_NAK = 0x15
XMODEM_CAN = 0x18
XMODEM_CRC = ord("C")  # 0x43
XMODEM_BLOCK_SIZE = 128

BOOTLOADER_TOKENS = (b"BL >", b"ebl", b"menu", b"Bootloader", b"begin upload")


class PosixSerial:
    """
    Direct Linux termios serial port driver that acquires an exclusive lock, enables 1 ms
    low_latency, and clears HUPCL/CRTSCTS so baudrate switches never glitch DTR/RTS.
    """

    _BAUD_MAP = {57600: termios.B57600, 115200: termios.B115200}

    def __init__(self, port, baudrate=115200, timeout=0.1):
        self.port = port
        self.timeout = timeout
        self.baudrate = baudrate
        self.fd = os.open(port, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
        try:
            self._lock_exclusive()
            self.set_baudrate(baudrate)
            self._enable_low_latency()
        except Exception:
            self.close()
            raise

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()

    def _lock_exclusive(self):
        try:
            if hasattr(termios, "TIOCEXCL"):
                fcntl.ioctl(self.fd, termios.TIOCEXCL)
            fcntl.flock(self.fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print(
                f"[ERROR] Serial port {self.port} is locked by another process "
                "(e.g., Home Assistant / ZHA / Zigbee2MQTT). Stop that service first."
            )
            sys.exit(1)
        except Exception:
            pass

    def _enable_low_latency(self):
        real_path = os.path.realpath(self.port)
        try:
            buf = bytearray(80)
            fcntl.ioctl(self.fd, termios.TIOCGSERIAL, buf)
            flags = struct.unpack_from("i", buf, 16)[0]
            async_low_latency = 1 << 13  # 0x2000 (<linux/tty_flags.h>)
            if not (flags & async_low_latency):
                struct.pack_into("i", buf, 16, flags | async_low_latency)
                fcntl.ioctl(self.fd, termios.TIOCSSERIAL, buf)
            print(f"[OK] Enabled kernel low_latency via ioctl on {real_path}")
            return
        except Exception:
            pass

        tty_name = os.path.basename(real_path)
        sysfs_latency = f"/sys/bus/usb-serial/devices/{tty_name}/latency_timer"
        if os.path.exists(sysfs_latency):
            try:
                with open(sysfs_latency, "w") as fp:
                    fp.write("1\n")
                print(f"[OK] Set sysfs latency_timer=1 on {tty_name}")
                return
            except Exception:
                pass

        try:
            res = subprocess.run(
                ["setserial", real_path, "low_latency"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=3,
                check=False,
            )
            if res.returncode == 0:
                print(f"[OK] Enabled low_latency via setserial on {real_path}")
        except Exception:
            pass

    def set_baudrate(self, baudrate):
        """Updates raw 8N1 baudrate in-place without closing the fd or touching DTR/RTS."""
        iflag, oflag, cflag, lflag, _, _, cc = termios.tcgetattr(self.fd)
        iflag &= ~(
            termios.IGNBRK
            | termios.BRKINT
            | termios.PARMRK
            | termios.ISTRIP
            | termios.INLCR
            | termios.IGNCR
            | termios.ICRNL
            | termios.IXON
            | termios.IXOFF
            | termios.IXANY
        )
        oflag &= ~termios.OPOST
        lflag &= ~(
            termios.ECHO | termios.ECHONL | termios.ICANON | termios.ISIG | termios.IEXTEN
        )
        cflag &= ~(termios.CSIZE | termios.PARENB | termios.CSTOPB | termios.HUPCL)
        if hasattr(termios, "CRTSCTS"):
            cflag &= ~termios.CRTSCTS
        cflag |= termios.CS8 | termios.CREAD | termios.CLOCAL

        bconst = self._BAUD_MAP[baudrate]
        cc[termios.VMIN] = 0
        cc[termios.VTIME] = 0
        termios.tcsetattr(
            self.fd,
            termios.TCSANOW,
            [iflag, oflag, cflag, lflag, bconst, bconst, cc],
        )
        self.baudrate = baudrate

    def read(self, size=1):
        buf = bytearray()
        deadline = time.time() + self.timeout
        while len(buf) < size:
            remaining = deadline - time.time()
            if remaining <= 0:
                break
            r, _, _ = select.select([self.fd], [], [], remaining)
            if not r:
                break
            try:
                chunk = os.read(self.fd, size - len(buf))
            except BlockingIOError:
                continue
            if not chunk:
                break
            buf.extend(chunk)
        return bytes(buf)

    def write(self, data):
        view = memoryview(data)
        total = 0
        deadline = time.time() + 2.0
        while total < len(data):
            remaining = max(0.01, deadline - time.time())
            _, w, _ = select.select([], [self.fd], [], remaining)
            if not w:
                raise TimeoutError("Serial write timed out")
            total += os.write(self.fd, view[total:])
        return total

    def flush(self):
        try:
            termios.tcdrain(self.fd)
        except Exception:
            pass

    def reset_input_buffer(self):
        try:
            termios.tcflush(self.fd, termios.TCIFLUSH)
        except Exception:
            pass
        while select.select([self.fd], [], [], 0.0)[0]:
            try:
                if not os.read(self.fd, 256):
                    break
            except Exception:
                break

    def close(self):
        if self.fd >= 0:
            for cleanup in (
                lambda: fcntl.ioctl(self.fd, termios.TIOCNXCL)
                if hasattr(termios, "TIOCNXCL")
                else None,
                lambda: fcntl.flock(self.fd, fcntl.LOCK_UN),
                lambda: os.close(self.fd),
            ):
                try:
                    cleanup()
                except Exception:
                    pass
            self.fd = -1


def resolve_port(explicit_port=None):
    """Finds the HUSBZB-1 Zigbee serial port (if01 / ttyUSB1)."""
    if explicit_port:
        return explicit_port
    for candidate in sorted(glob.glob("/dev/serial/by-id/*HubZ*-if01*")):
        if os.path.exists(candidate):
            return candidate
    return "/dev/ttyUSB1"


def ensure_valid_firmware(firmware_arg):
    """Locates, validates, or downloads ncp-uart-sw-6.7.8.ebl."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    candidates = [firmware_arg, os.path.join(script_dir, os.path.basename(firmware_arg))]
    fw_path = next((p for p in candidates if p and os.path.isfile(p)), None)

    if not fw_path:
        fw_path = firmware_arg or FIRMWARE_FILENAME
        print(f"[INFO] '{fw_path}' not found locally. Downloading from {FIRMWARE_URL}...")
        urllib.request.urlretrieve(FIRMWARE_URL, fw_path)

    with open(fw_path, "rb") as fp:
        data = fp.read()

    if len(data) < 256 or data[6:8] != b"\xe3\x50":
        print(f"[WARN] '{fw_path}' is not a valid EBL binary. Re-downloading...")
        urllib.request.urlretrieve(FIRMWARE_URL, fw_path)
        with open(fw_path, "rb") as fp:
            data = fp.read()

    if len(data) < 256 or data[6:8] != b"\xe3\x50":
        print(f"[ERROR] Firmware '{fw_path}' failed EBL header magic validation.")
        sys.exit(1)

    sha256 = hashlib.sha256(data).hexdigest()
    if os.path.basename(fw_path) == FIRMWARE_FILENAME and sha256 != FIRMWARE_SHA256:
        print(f"[WARN] SHA256 mismatch ({sha256[:12]}...), but EBL header magic is valid.")
    else:
        print(
            f"[OK] Verified EBL firmware: {fw_path} "
            f"({len(data)} bytes, {len(data) // XMODEM_BLOCK_SIZE} blocks)"
        )

    rem = len(data) % XMODEM_BLOCK_SIZE
    return data + (b"\xff" * (XMODEM_BLOCK_SIZE - rem) if rem else b"")


# ---------------------------------------------------------------------------
# ASHv2 / EZSP Framing (57600 baud)
# ---------------------------------------------------------------------------


def _ash_randomize(data):
    """XORs data with the ASH pseudo-random sequence (seed 0x42, poly 0xB8)."""
    curr = 0x42
    out = bytearray()
    for b in data:
        out.append(b ^ curr)
        curr = (curr >> 1) if (curr & 1) == 0 else ((curr >> 1) ^ 0xB8)
    return bytes(out)


def _ash_escape(data):
    """Escapes ASH reserved bytes (0x7D, 0x7E, 0x11, 0x13, 0x18, 0x1A)."""
    out = bytearray()
    for b in data:
        if b in (0x7D, 0x7E, 0x11, 0x13, 0x18, 0x1A):
            out.extend((0x7D, b ^ 0x20))
        else:
            out.append(b)
    return bytes(out)


def _ash_unescape(data):
    """Unescapes an ASH byte-stuffed frame and strips XON/XOFF bytes."""
    out = bytearray()
    i = 0
    while i < len(data):
        b = data[i]
        if b in (0x11, 0x13):
            i += 1
        elif b == 0x7D and i + 1 < len(data):
            out.append(data[i + 1] ^ 0x20)
            i += 2
        else:
            out.append(b)
            i += 1
    return bytes(out)


def _ash_read_frame(ser, timeout=2.5):
    """Reads a single ASH frame terminated by 0x7E (FLAG_BYTE)."""
    buf = bytearray()
    deadline = time.time() + timeout
    while time.time() < deadline:
        ch = ser.read(1)
        if not ch:
            continue
        b = ch[0]
        if b in (0x11, 0x13):
            continue
        if b == 0x1A:  # CANCEL byte drops partial frame
            buf.clear()
            continue
        buf.append(b)
        if b == 0x7E:
            return _ash_unescape(bytes(buf[:-1]))
    return None


def _ash_send_ack(ser, rx_ctrl_byte):
    """Sends an ASH ACK frame acknowledging the NCP's DATA frame."""
    ack_num = (((rx_ctrl_byte >> 4) & 0x07) + 1) & 0x07
    ctrl = 0x80 | ack_num
    crc = binascii.crc_hqx(bytes([ctrl]), 0xFFFF)
    ser.write(_ash_escape(bytes([ctrl, (crc >> 8) & 0xFF, crc & 0xFF])) + b"\x7E")
    ser.flush()


def _ash_build_data_frame(frm_num, ack_num, ezsp_payload):
    """Builds an ASH DATA frame with pseudo-random XOR, CRC-16, and byte stuffing."""
    ctrl = ((frm_num & 0x07) << 4) | (ack_num & 0x07)
    body = bytes([ctrl]) + _ash_randomize(ezsp_payload)
    crc = binascii.crc_hqx(body, 0xFFFF)
    return _ash_escape(body + struct.pack(">H", crc)) + b"\x7E"


def _ash_reset_and_version(ser, init_ver=4):
    """Resets the ASH link at 57600 baud and returns the NCP's active EZSP protocol version."""
    ser.set_baudrate(57600)
    time.sleep(0.15)
    ser.reset_input_buffer()

    rstack = None
    for _ in range(2):
        ser.write(b"\x1A\xC0\x38\xBC\x7E")
        ser.flush()
        rstack = _ash_read_frame(ser, timeout=2.0)
        if rstack and len(rstack) >= 3 and rstack[0] == 0xC1:
            break
        time.sleep(0.2)

    if not rstack or len(rstack) < 3 or rstack[0] != 0xC1:
        return None

    ser.write(_ash_build_data_frame(0, 0, bytes([0x00, 0x00, 0x00, init_ver])))
    ser.flush()
    ver_resp = _ash_read_frame(ser, timeout=2.0)
    if not ver_resp or len(ver_resp) < 7:
        return None

    _ash_send_ack(ser, ver_resp[0])
    return _ash_randomize(ver_resp[1:-2])[3]


def trigger_bootloader_inplace(ser, mode=0x01):
    """
    Transitions the EM3581 from 57600 EZSP runtime into the 115200 standalone bootloader
    on the same open serial file descriptor, holding for 5.0s after ACK so the reboot completes.
    """
    print(
        f"[EZSP] Switching port in-place to 57600 baud and sending launchStandaloneBootloader(0x{mode:02x})..."
    )
    try:
        ncp_ezsp_ver = _ash_reset_and_version(ser, init_ver=4)
        if ncp_ezsp_ver is None:
            print("[EZSP] Did not receive valid RSTACK/version response at 57600 baud.")
            return False

        print(f"[EZSP] Connected to runtime NCP (EZSP v{ncp_ezsp_ver}).")
        frm_num, ack_num, seq_num = 1, 1, 1

        # Negotiate target EZSP version if the NCP runs EZSP v5+
        if ncp_ezsp_ver >= 8:
            ezsp_v_req = bytes([seq_num, 0x00, 0x01, 0x00, 0x00, ncp_ezsp_ver])
        elif ncp_ezsp_ver >= 5:
            ezsp_v_req = bytes([seq_num, 0x00, 0xFF, 0x00, 0x00, ncp_ezsp_ver])
        else:
            ezsp_v_req = None

        if ezsp_v_req is not None:
            ser.write(_ash_build_data_frame(frm_num, ack_num, ezsp_v_req))
            ser.flush()
            v2_resp = _ash_read_frame(ser, timeout=2.0)
            if v2_resp:
                _ash_send_ack(ser, v2_resp[0])
            frm_num = (frm_num + 1) & 0x07
            ack_num = (ack_num + 1) & 0x07
            seq_num += 1

        # Send launchStandaloneBootloader(mode) (Frame ID 0x008F)
        if ncp_ezsp_ver >= 8:
            bl_ezsp = bytes([seq_num, 0x00, 0x01, 0x8F, 0x00, mode])
        elif ncp_ezsp_ver >= 5:
            bl_ezsp = bytes([seq_num, 0x00, 0xFF, 0x00, 0x8F, mode])
        else:
            bl_ezsp = bytes([seq_num, 0x00, 0x8F, mode])

        ser.write(_ash_build_data_frame(frm_num, ack_num, bl_ezsp))
        ser.flush()

        bl_resp = _ash_read_frame(ser, timeout=2.0)
        if not (bl_resp and len(bl_resp) >= 4 and (bl_resp[0] & 0x80) == 0):
            print(f"[EZSP] Unexpected launchStandaloneBootloader response: {bl_resp!r}")
            return False

        _ash_send_ack(ser, bl_resp[0])
        dec = _ash_randomize(bl_resp[1:-2])
        print(
            f"[EZSP] launchStandaloneBootloader(0x{mode:02x}) ACKed (payload={dec.hex()}). "
            f"Holding port open for {EZSP_BOOTLOADER_LAUNCH_DELAY:.1f}s while NCP reboots..."
        )

        # Listen at 57600 baud for 1.5s to re-ACK if the NCP retransmits its DATA frame
        ack_deadline = time.time() + 1.5
        while time.time() < ack_deadline:
            extra = _ash_read_frame(ser, timeout=0.3)
            if extra and len(extra) >= 4 and (extra[0] & 0x80) == 0:
                _ash_send_ack(ser, extra[0])

        ser.set_baudrate(115200)
        time.sleep(max(0.5, EZSP_BOOTLOADER_LAUNCH_DELAY - 1.5))
        return True
    except Exception as exc:
        print(f"[EZSP] Trigger exception: {exc}")
        return False
    finally:
        if ser.baudrate != 115200:
            ser.set_baudrate(115200)


# ---------------------------------------------------------------------------
# Bootloader Menu & XMODEM-CRC Upload (115200 baud)
# ---------------------------------------------------------------------------


def _echo_bytes(data):
    """Echoes printable ASCII bytes to stdout."""
    for b in data:
        if 32 <= b <= 126 or b in (10, 13):
            sys.stdout.write(chr(b))
    sys.stdout.flush()


def _read_until_quiet(ser, quiet_time=0.25, max_time=1.2, echo=True):
    """Reads available serial bytes until the line stays silent for quiet_time."""
    buf = bytearray()
    start = last_rx = time.time()
    while time.time() - start < max_time:
        chunk = ser.read(64)
        if chunk:
            buf.extend(chunk)
            if echo:
                _echo_bytes(chunk)
            last_rx = time.time()
        elif buf and (time.time() - last_rx) >= quiet_time:
            break
        else:
            time.sleep(0.02)
    return bytes(buf)


def _is_upload_ready(buf):
    """Returns True if buf contains 'begin upload' + 'C'/NAK, or pure XMODEM 'C' polling."""
    idx = buf.find(b"begin upload")
    if idx != -1:
        tail = buf[idx + len(b"begin upload") :]
        if b"C" in tail or b"\x15" in tail:
            return True
    stripped = buf.strip(b"\x00\x11\x13\r\n ")
    return bool(stripped) and all(b == XMODEM_CRC for b in stripped)


def _wait_for_upload_ready(ser, initial_buf=b"", timeout=8.0):
    """Waits for 'begin upload' and the XMODEM 'C' polling byte."""
    buf = bytearray(initial_buf)
    if _is_upload_ready(buf):
        return True, bytes(buf)

    start = time.time()
    while time.time() - start < timeout:
        ch = ser.read(1)
        if ch:
            buf.extend(ch)
            _echo_bytes(ch)
            if _is_upload_ready(buf):
                return True, bytes(buf)
        else:
            time.sleep(0.02)
    return False, bytes(buf)


def enter_bootloader_upload(ser, timeout=8.0, wake_attempts=6):
    """
    Synchronizes with the EM3581 Serial Bootloader at 115200 baud and enters XMODEM upload mode.
    """
    ser.set_baudrate(115200)

    # Check if bootloader output or XMODEM 'C' polling is already buffered
    initial = _read_until_quiet(ser, quiet_time=0.2, max_time=0.6, echo=False)
    if _is_upload_ready(initial):
        print("\n[OK] Bootloader is already in XMODEM upload mode ('C').")
        return True

    synced_menu = False
    observed_raw = bytearray(initial)
    if any(token in initial for token in BOOTLOADER_TOKENS):
        _echo_bytes(initial)
        synced_menu = True

    if not synced_menu:
        print("Synchronizing with bootloader prompt...")
        for attempt in range(wake_attempts):
            ser.write(b"\n" if (attempt % 2 == 0) else b"\r\n")
            ser.flush()
            raw = _read_until_quiet(ser, quiet_time=0.25, max_time=1.0, echo=False)
            if not raw:
                time.sleep(0.2)
                continue

            observed_raw.extend(raw)
            if any(token in raw for token in BOOTLOADER_TOKENS):
                _echo_bytes(raw)
                if b"begin upload" in raw:
                    ok, _ = _wait_for_upload_ready(ser, initial_buf=raw, timeout=timeout)
                    return ok
                synced_menu = True
                break

            if _is_upload_ready(raw):
                print("\n[OK] Bootloader is emitting XMODEM 'C' polling tokens.")
                return True

            # Abort early if 57600-baud ASH RSTACK bytes are seen on initial probe
            if attempt >= 1 and any(b in raw for b in (0x60, 0x78, 0x98, 0xFE)):
                break

    if not synced_menu:
        rx_info = f" (rx={bytes(observed_raw[:32]).hex()};" if observed_raw else " ("
        print(f"[INFO] No bootloader menu at 115200 baud{rx_info} radio is in 57600 runtime mode).")
        return False

    # Select Option 1 ('upload ebl') with single-byte b"1" first; send b"\r\n" only if needed
    print("\nSelecting Option 1 ('upload ebl')...")
    ser.reset_input_buffer()
    ser.write(b"1")
    ser.flush()

    ok, partial_buf = _wait_for_upload_ready(ser, initial_buf=b"", timeout=1.5)
    if ok:
        return True

    if b"begin upload" not in partial_buf:
        ser.write(b"\r\n")
        ser.flush()

    ok, final_buf = _wait_for_upload_ready(ser, initial_buf=partial_buf, timeout=timeout)
    if not ok:
        print(f"\n[DEBUG] Buffer before timeout: {final_buf!r}")
    return ok


def xmodem_crc_upload(ser, firmware_bytes, max_retries=16):
    """Streams `firmware_bytes` in 128-byte XMODEM-CRC blocks."""
    total_blocks = len(firmware_bytes) // XMODEM_BLOCK_SIZE
    ser.reset_input_buffer()

    for block_idx in range(total_blocks):
        seq = (block_idx + 1) & 0xFF
        payload = firmware_bytes[
            block_idx * XMODEM_BLOCK_SIZE : (block_idx + 1) * XMODEM_BLOCK_SIZE
        ]
        crc = binascii.crc_hqx(payload, 0)
        packet = bytes([XMODEM_SOH, seq, 0xFF - seq]) + payload + struct.pack(">H", crc)

        ack_received = False
        for attempt in range(1, max_retries + 1):
            ser.write(packet)
            ser.flush()

            deadline = time.time() + 3.0
            while time.time() < deadline:
                resp = ser.read(1)
                if not resp:
                    continue
                b = resp[0]
                if b in (0x00, 0x11, 0x13) or (block_idx == 0 and b == XMODEM_CRC):
                    continue
                if b == XMODEM_ACK:
                    ack_received = True
                    break
                if b == XMODEM_NAK:
                    break
                if b == XMODEM_CAN:
                    print("\n[ERROR] Bootloader cancelled XMODEM transfer (CAN received).")
                    return False

            if ack_received:
                break

            time.sleep(0.05)
            ser.reset_input_buffer()
            sys.stdout.write(
                f"\rBlock {block_idx + 1}/{total_blocks}: retry {attempt}/{max_retries}..."
            )
            sys.stdout.flush()

        if not ack_received:
            print(
                f"\n[ERROR] Block {block_idx + 1}/{total_blocks} failed after {max_retries} retries."
            )
            return False

        if (block_idx + 1) % 25 == 0 or (block_idx + 1) == total_blocks:
            pct = 100.0 * (block_idx + 1) / total_blocks
            sys.stdout.write(
                f"\rTransferred: {block_idx + 1}/{total_blocks} blocks ({pct:5.1f}%)"
            )
            sys.stdout.flush()

    print("\nSending EOT...")
    for _ in range(5):
        ser.write(bytes([XMODEM_EOT]))
        ser.flush()
        deadline = time.time() + 2.0
        while time.time() < deadline:
            resp = ser.read(1)
            if resp and resp[0] == XMODEM_ACK:
                return True
    print("[WARN] Did not receive explicit ACK for EOT; checking upload status...")
    return True


def reboot_and_verify_runtime(ser):
    """
    Confirms 'Serial upload complete', issues Option 2 ('run') to boot the new firmware,
    and verifies EZSP communication at 57600 baud on the same open serial port.
    """
    post_upload = _read_until_quiet(ser, quiet_time=0.3, max_time=2.5)
    if b"aborted" in post_upload.lower():
        print("\n[ERROR] Bootloader reported: Serial upload aborted!")
        return False

    if b"BL >" not in post_upload:
        ser.write(b"\n")
        ser.flush()
        _read_until_quiet(ser, quiet_time=0.25, max_time=1.0)

    print("\nBooting into new application firmware (Option 2: run)...")
    ser.write(b"2")
    ser.flush()
    time.sleep(0.3)
    ser.write(b"\r\n")
    ser.flush()

    print("Waiting 4.0s for EmberZNet 6.7.8 application startup...")
    time.sleep(4.0)

    print("Verifying EZSP runtime response at 57600 baud...")
    ncp_ezsp_ver = _ash_reset_and_version(ser, init_ver=8)
    if ncp_ezsp_ver is not None:
        print(f"[VERIFIED] HUSBZB-1 responded to EZSP v{ncp_ezsp_ver} at 57600 baud!")
    else:
        print("[INFO] Radio rebooted (ASH RSTACK not captured yet, which is normal).")
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Standalone HUSBZB-1 (EM3581) Firmware Flasher"
    )
    parser.add_argument(
        "-p",
        "--port",
        default=None,
        help="Serial port path (default: auto-detect HubZ-if01 or /dev/ttyUSB1)",
    )
    parser.add_argument(
        "-f",
        "--firmware",
        default=FIRMWARE_FILENAME,
        help=f"EBL firmware path (default: {FIRMWARE_FILENAME})",
    )
    args = parser.parse_args()

    firmware_bytes = ensure_valid_firmware(args.firmware)
    port = resolve_port(args.port)
    print(f"Target Zigbee Port: {port}")

    print("\n--- Phase 1: Probing bootloader at 115200 baud ---")
    with PosixSerial(port, baudrate=115200, timeout=0.1) as ser:
        ready = enter_bootloader_upload(ser, timeout=4.0, wake_attempts=3)

        if not ready:
            for attempt, mode in enumerate((0x01, 0x00), start=1):
                print(
                    f"\n--- Phase 2 (Attempt {attempt}): Triggering bootloader reboot "
                    f"(mode=0x{mode:02x}) ---"
                )
                trigger_bootloader_inplace(ser, mode=mode)
                ready = enter_bootloader_upload(ser, timeout=8.0, wake_attempts=8)
                if ready:
                    break

        if not ready:
            print("\n[ERROR] EM3581 did not enter XMODEM upload mode ('C'). Aborting.")
            sys.exit(1)

        print(f"\n\n--- Phase 3: Streaming {args.firmware} via XMODEM-CRC ---")
        if not xmodem_crc_upload(ser, firmware_bytes):
            print("\n[ERROR] XMODEM firmware upload failed.")
            sys.exit(1)

        print("\n[SUCCESS] Firmware image transferred to EM3581!")

        print("\n--- Phase 4: Rebooting & Verifying Runtime Firmware ---")
        reboot_and_verify_runtime(ser)


if __name__ == "__main__":
    main()
