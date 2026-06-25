#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
EasyADB - Interactive ADB Tool
Developer: DangerousAngel

A comprehensive menu-driven interface for Android ADB operations.
Supports backup/decryption, file management, app control, system tweaks,
and advanced utilities like contact extraction and file searching.
"""

import sys
import os
import subprocess
import tarfile
import tempfile
import re
from getpass import getpass
from binascii import a2b_hex
import socket

# ----------------------------------------------------------------------
# Embedded abpy (minimal) for backup decryption
# ----------------------------------------------------------------------

READ_BUF_SIZE = 128 * 1024
MAX_DECOMPRESS_SIZE = 512 * 1024

class BadABBody(Exception):
    pass

class BadABHeader(Exception):
    pass

def read_header(infile):
    if infile.read(15) != b"ANDROID BACKUP\n":
        raise BadABHeader("bad first 15 bytes of file")
    version = str(infile.readline(32), "ascii")
    if version[-1:] != "\n":
        raise BadABHeader("failed to read version in file")
    version = int(version)
    compressed = infile.read(2)
    if compressed == b"0\n":
        compressed = False
    elif compressed == b"1\n":
        compressed = True
    else:
        raise BadABHeader("bad compression flag in file")
    e = infile.read(5)
    if e == b"none\n":
        return version, compressed, None
    if e != b"AES-2" or infile.read(3) != b"56\n":
        raise BadABHeader("bad encryption method in file")
    password_salt = infile.read(129)
    if password_salt[128:] != b"\n":
        raise BadABHeader("failed to read password salt in file")
    password_salt = a2b_hex(password_salt[:128])
    master_key_checksum_salt = infile.read(129)
    if master_key_checksum_salt[128:] != b"\n":
        raise BadABHeader("failed to read master key checksum in file")
    master_key_checksum_salt = a2b_hex(master_key_checksum_salt[:128])
    rounds = str(infile.readline(32), "ascii")
    if rounds[-1:] != "\n":
        raise BadABHeader("failed to read rounds in file")
    rounds = int(rounds)
    if rounds < 1:
        raise BadABHeader("rounds < 1")
    master_key_blob_iv = infile.read(33)
    if master_key_blob_iv[32:] != b"\n":
        raise BadABHeader("failed to read master key blob iv in file")
    master_key_blob_iv = a2b_hex(master_key_blob_iv[:32])
    master_key_blob = infile.read(193)
    if master_key_blob[192:] != b"\n":
        raise BadABHeader("failed to read master key blob in file")
    master_key_blob = a2b_hex(master_key_blob[:192])
    return version, compressed, (password_salt, master_key_checksum_salt, rounds, master_key_blob_iv, master_key_blob)

def pbkdf2engine(name):
    if name is None or name == "hashlib":
        from hashlib import pbkdf2_hmac
        return lambda password, salt, dkLen, count: pbkdf2_hmac("sha1", password, salt, count, dkLen)
    if name == "pycryptodome":
        from Crypto.Protocol.KDF import PBKDF2
    elif name == "pycryptodomex":
        from Cryptodome.Protocol.KDF import PBKDF2
    else:
        assert False
    return PBKDF2

def aes256engine(name):
    if name is None or name == "afalg":
        if hasattr(socket, "AF_ALG"):
            def make_socket(key):
                with socket.socket(38, 5) as s1:
                    s1.bind(("skcipher", "cbc(aes)"))
                    s1.setsockopt(279, 1, key)
                    return s1.accept()[0]
        else:
            from _rawffi.alt import get_libc, types
            libc = get_libc()
            libc_bind = libc.getfunc("bind", (types.sint, types.char_p, types.sint), types.sint)
            libc_accept4 = libc.getfunc("accept4", (types.sint, types.void_p, types.void_p, types.sint), types.sint)
            def make_socket(key):
                with socket.socket(38, 5) as s1:
                    if libc_bind(s1.fileno(), pack("h22s64s", 38, b"skcipher", b"cbc(aes)"), 88):
                        raise OSError("bind failed")
                    s1.setsockopt(279, 1, key)
                    s2fd = libc_accept4(s1.fileno(), 0, 0, socket.SOCK_CLOEXEC)
                    if s2fd < 0:
                        raise OSError("accept4 failed")
                    return socket.socket(38, 5, 0, s2fd)
        def makehandle(encrypt, key, iv):
            assert len(key) == 32
            assert len(iv) == 16
            return make_socket(key), [(279, 3, pack("i", encrypt)), (279, 2, pack("i16s", 16, iv))]
        def closehandle(handle):
            handle[0].close()
        def strictrecv(sock, size, unpad):
            rbuf = sock.recv(size)
            if len(rbuf) != size:
                raise Exception("short recv")
            if unpad:
                padsize = rbuf[-1]
                if padsize not in range(1, 17):
                    raise BadABBody("invalid decrypted padding last byte")
                if rbuf.count(padsize, -padsize) != padsize:
                    raise BadABBody("decrypted padding bytes not all equal")
                if len(rbuf) == padsize:
                    raise StopIteration
                return memoryview(rbuf)[:-padsize]
            return rbuf
        def transform(handle, inbufs, unpad):
            sock, ancdata = handle
            while inbufs:
                slen = slen2 = sock.sendmsg(inbufs, ancdata, 32832)
                if not slen:
                    raise Exception("sendmsg returned 0")
                if 15 & slen:
                    raise Exception("sendmsg returned number not divisible by 16")
                ancdata.clear()
                for i, inbuf in enumerate(inbufs, 1):
                    slen2 -= len(inbuf)
                    if slen2 <= 0:
                        break
                else:
                    assert False
                inbufs[:i] = (memoryview(inbuf)[slen2:],) if slen2 else ()
                del inbuf
                try:
                    yield strictrecv(sock, slen, unpad and not inbufs)
                except StopIteration:
                    return
    else:
        if name == "pycryptodome":
            from Crypto.Cipher.AES import new
        elif name == "pycryptodomex":
            from Cryptodome.Cipher.AES import new
        else:
            assert False
        def makehandle(encrypt, key, iv):
            assert len(key) == 32
            assert len(iv) == 16
            x = new(key, 2, iv=iv)
            return x.encrypt if encrypt else x.decrypt
        def closehandle(handle):
            pass
        bytearrayjoin = bytearray().join
        def non_generator_transform(handle, inbufs, unpad):
            if len(inbufs) == 1:
                inbuf = inbufs[0]
                outbuf = bytearray(len(inbuf))
            else:
                inbuf = outbuf = bytearrayjoin(inbufs)
            inbufs.clear()
            handle(inbuf, outbuf)
            if unpad:
                padsize = outbuf[-1]
                if padsize not in range(1, 17):
                    raise BadABBody("invalid decrypted padding last byte")
                if outbuf.count(padsize, -padsize) != padsize:
                    raise BadABBody("decrypted padding bytes not all equal")
                if len(inbuf) == padsize:
                    raise StopIteration
                return memoryview(outbuf)[:-padsize]
            return outbuf
        def transform(handle, inbufs, unpad):
            try:
                yield non_generator_transform(handle, inbufs, unpad)
            except StopIteration:
                pass
    return makehandle, closehandle, transform

def decypt_from_file(infile, handle, transform):
    tail16 = infile.read(16)
    if len(tail16) != 16:
        raise BadABBody("encrypted body size less than 16")
    while True:
        chunk = infile.read(READ_BUF_SIZE)
        if not chunk:
            yield from transform(handle, [tail16], True)
            return
        chunksize = len(chunk)
        if 15 & chunksize:
            raise BadABBody("encrypted body size not divisible by 16")
        if chunksize != READ_BUF_SIZE:
            decryptlist = [tail16, chunk]
            del chunk
            yield from transform(handle, decryptlist, True)
            return
        decryptlist = [tail16, memoryview(chunk)[:-16]]
        tail16 = chunk[-16:]
        del chunk
        yield from transform(handle, decryptlist, False)

def decompress_from_iterator(initer):
    from zlib import decompressobj
    d = decompressobj(15)
    try:
        while not d.eof:
            yield d.decompress(next(initer), MAX_DECOMPRESS_SIZE)
            while d.unconsumed_tail:
                yield d.decompress(d.unconsumed_tail, MAX_DECOMPRESS_SIZE)
    except StopIteration:
        raise BadABBody("end of file without zlib trailer")
    if d.unused_data or next(initer, False):
        raise BadABBody("data after zlib trailer")

def ab2tar_main(infile, outfile, password=None, chk=False,
                pbkdf2engine_name=None, aes256engine_name=None):
    version, compressed, encryption_info = read_header(infile)
    if encryption_info is None:
        if password is not None:
            sys.stderr.write("warning: password argument unused\n")
        if chk:
            sys.stderr.write("warning: chk argument unused\n")
        if pbkdf2engine_name is not None:
            sys.stderr.write("warning: pbkdf2engine argument unused\n")
        if aes256engine_name is not None:
            sys.stderr.write("warning: aes256engine argument unused\n")
        initer = iter(lambda: infile.read1(READ_BUF_SIZE), b"")
    else:
        pbkdf2 = pbkdf2engine(pbkdf2engine_name)
        aes256createhandle, aes256closehandle, aes256transform = aes256engine(aes256engine_name)
        password_salt, master_key_checksum_salt, rounds, master_key_blob_iv, master_key_blob = encryption_info
        if password is None:
            password = bytes(getpass("enter password -> "), "ascii")
        aes256handle = aes256createhandle(False,
                                          pbkdf2(password, password_salt, 32, rounds),
                                          master_key_blob_iv)
        m = b"".join(aes256transform(aes256handle, [master_key_blob], False))
        aes256closehandle(aes256handle)
        if m[0] != 16 or m[17] != 32 or m[50] != 32 or m[83:] != b"\r\r\r\r\r\r\r\r\r\r\r\r\r":
            sys.stderr.write("invalid decrypted master key blob\nwrong password?\n")
            sys.exit(1)
        master_key = m[18:50]
        master_key_checksum = m[51:83]
        if chk and pbkdf2(master_key, master_key_checksum_salt, 32, rounds) != master_key_checksum and (
            all(x < 0x80 for x in master_key) or pbkdf2(
                bytes("".join(chr(x if x < 0x80 else x + 0xff00) for x in master_key), "utf8"),
                master_key_checksum_salt, 32, rounds
            ) != master_key_checksum
        ):
            sys.stderr.write("bad master key checksum\n(validation not skipped because chk argument)\nwrong password?\n")
            sys.exit(1)
        initer = decypt_from_file(infile,
                                  aes256createhandle(False, master_key, m[1:17]),
                                  aes256transform)
    final_iter = decompress_from_iterator(initer) if compressed else initer
    for chunk in final_iter:
        outfile.write(chunk)
    outfile.flush()

def convert_ab_to_tar(ab_file, tar_file, password=None):
    with open(ab_file, "rb") as inf:
        with open(tar_file, "wb") as outf:
            ab2tar_main(inf, outf, password=password, chk=False,
                        pbkdf2engine_name="hashlib", aes256engine_name="afalg")

# ----------------------------------------------------------------------
# Core ADB functions
# ----------------------------------------------------------------------

def check_adb():
    try:
        subprocess.run(["adb", "version"], capture_output=True, check=True)
        return True
    except:
        return False

def run_adb(args, capture_output=False, check=True):
    cmd = ["adb"] + args
    result = subprocess.run(cmd, capture_output=capture_output, text=True)
    if check and result.returncode != 0:
        sys.stderr.write(f"adb command failed: {' '.join(cmd)}\n")
        if result.stderr:
            sys.stderr.write(result.stderr)
        return None if capture_output else False
    return result.stdout if capture_output else True

def run_adb_shell_command(cmd_str, capture_output=True):
    return run_adb(["shell", cmd_str], capture_output=True)

# ----------------------------------------------------------------------
# Menu functions (each corresponds to a service)
# ----------------------------------------------------------------------

def menu_pull():
    src = input("Enter source path on device: ").strip()
    dest = input("Enter destination path on local: ").strip()
    if src and dest:
        print(f"Pulling {src} to {dest}...")
        run_adb(["pull", src, dest])

def menu_push():
    src = input("Enter local source path: ").strip()
    dest = input("Enter destination path on device: ").strip()
    if src and dest:
        print(f"Pushing {src} to {dest}...")
        run_adb(["push", src, dest])

def menu_install():
    apk = input("Enter path to APK file: ").strip()
    if apk:
        print(f"Installing {apk}...")
        run_adb(["install", apk])

def menu_list_packages():
    pattern = input("Enter pattern to search (leave empty for all): ").strip()
    out = run_adb(["shell", "pm", "list", "packages"], capture_output=True)
    if out:
        lines = out.splitlines()
        if pattern:
            lines = [l for l in lines if pattern in l]
        for line in lines:
            print(line)

def menu_clear():
    pkg = input("Enter package name: ").strip()
    if pkg:
        print(f"Clearing data for {pkg}...")
        run_adb(["shell", "pm", "clear", pkg])

def menu_uninstall():
    pkg = input("Enter package name: ").strip()
    if not pkg:
        return
    user0 = input("Uninstall for user 0? (y/n): ").strip().lower() == 'y'
    cmd = ["shell", "pm", "uninstall"]
    if user0:
        cmd += ["--user", "0"]
    cmd.append(pkg)
    print(f"Uninstalling {pkg}...")
    run_adb(cmd)

def menu_ps():
    print("Running processes:")
    out = run_adb(["shell", "ps"], capture_output=True)
    if out:
        print(out)

def menu_force_stop():
    pkg = input("Enter package name: ").strip()
    if pkg:
        print(f"Force stopping {pkg}...")
        run_adb(["shell", "am", "force-stop", pkg])

def menu_start_activity():
    pkg = input("Enter package name: ").strip()
    act = input("Enter activity name (e.g., .MainActivity): ").strip()
    if pkg and act:
        print(f"Starting {pkg}/{act}...")
        run_adb(["shell", "am", "start", "-n", f"{pkg}/{act}"])

def menu_open_url():
    url = input("Enter URL: ").strip()
    if url:
        print(f"Opening {url}...")
        run_adb(["shell", "am", "start", "-a", "android.intent.action.VIEW", "-d", url])

def menu_setprop():
    prop = input("Enter property name: ").strip()
    val = input("Enter value: ").strip()
    if prop and val:
        print(f"Setting {prop}={val}...")
        run_adb(["shell", "setprop", prop, val])

def menu_broadcast():
    action = input("Enter intent action: ").strip()
    if not action:
        return
    extras = {}
    while True:
        add = input("Add extra? (key=value, or blank to finish): ").strip()
        if not add:
            break
        if '=' not in add:
            print("Invalid format. Use key=value")
            continue
        k, v = add.split('=', 1)
        # infer type
        if v.lower() == 'true':
            v = True
        elif v.lower() == 'false':
            v = False
        elif v.isdigit():
            v = int(v)
        else:
            try:
                v = float(v)
            except:
                pass
        extras[k] = v
    print(f"Broadcasting {action} with extras {extras}")
    cmd = ["shell", "am", "broadcast", "-a", action]
    for k, v in extras.items():
        if isinstance(v, bool):
            cmd += ["--ez", k, str(v).lower()]
        elif isinstance(v, int):
            cmd += ["--ei", k, str(v)]
        elif isinstance(v, float):
            cmd += ["--ef", k, str(v)]
        else:
            cmd += ["--es", k, str(v)]
    run_adb(cmd)

def menu_run_as():
    pkg = input("Enter package name: ").strip()
    cmd_str = input("Enter command to run (e.g., ls /data/data/...): ").strip()
    if pkg and cmd_str:
        print(f"Running as {pkg}: {cmd_str}")
        run_adb(["shell", "run-as", pkg] + cmd_str.split())

def menu_backup_decrypt():
    pkg = input("Enter package name to backup: ").strip()
    if not pkg:
        return
    with_apk = input("Include APK? (y/n): ").strip().lower() == 'y'
    output_tar = input("Output tar file name (default: package.tar): ").strip()
    if not output_tar:
        output_tar = f"{pkg}.tar"
    password = input("Password (if encrypted, leave blank to prompt later): ").strip()
    if password == "":
        password = None
    extract = input("Extract tar after conversion? (y/n): ").strip().lower() == 'y'

    ab_file = "backup.ab"
    print(f"Backing up {pkg} to {ab_file}...")
    apk_flag = "-apk" if with_apk else "-noapk"
    run_adb(["backup", "-f", ab_file, apk_flag, pkg])

    print(f"Converting {ab_file} to {output_tar}...")
    try:
        convert_ab_to_tar(ab_file, output_tar, password=password)
    except Exception as e:
        sys.stderr.write(f"Conversion failed: {e}\n")
        return

    if extract:
        extract_dir = os.path.splitext(output_tar)[0] + "_extracted"
        os.makedirs(extract_dir, exist_ok=True)
        print(f"Extracting {output_tar} to {extract_dir}...")
        with tarfile.open(output_tar, "r") as tar:
            tar.extractall(extract_dir)
        print(f"Extracted to {extract_dir}")

    print("Backup and decryption completed.")

def menu_screenshot():
    dest = input("Destination path for screenshot (e.g., screenshot.png): ").strip()
    if not dest:
        dest = "screenshot.png"
    print("Taking screenshot...")
    run_adb(["shell", "screencap", "-p", "/sdcard/screenshot.png"])
    run_adb(["pull", "/sdcard/screenshot.png", dest])
    run_adb(["shell", "rm", "/sdcard/screenshot.png"])
    print(f"Screenshot saved to {dest}")

def menu_screenrecord():
    duration = input("Record duration in seconds (default 30): ").strip()
    duration = int(duration) if duration.isdigit() else 30
    dest = input("Destination path for video (e.g., record.mp4): ").strip()
    if not dest:
        dest = "screenrecord.mp4"
    print(f"Recording screen for {duration}s...")
    run_adb(["shell", "screenrecord", "--time-limit", str(duration), "/sdcard/record.mp4"])
    run_adb(["pull", "/sdcard/record.mp4", dest])
    run_adb(["shell", "rm", "/sdcard/record.mp4"])
    print(f"Screen recording saved to {dest}")

def menu_device_info():
    print("\n=== DEVICE INFORMATION ===")
    props = [
        "ro.product.model", "ro.product.manufacturer", "ro.build.version.release",
        "ro.build.version.sdk", "ro.build.fingerprint", "ro.product.board",
        "ro.product.cpu.abi", "ro.product.device", "ro.build.date"
    ]
    for p in props:
        val = run_adb(["shell", "getprop", p], capture_output=True)
        if val:
            val = val.strip()
            print(f"{p}: {val}")
    # Battery
    print("\n--- Battery ---")
    batt = run_adb(["shell", "dumpsys", "battery"], capture_output=True)
    if batt:
        for line in batt.splitlines():
            if any(x in line for x in ["level", "status", "health", "temperature", "voltage"]):
                print(line.strip())
    # Storage
    print("\n--- Storage ---")
    storage = run_adb(["shell", "df", "-h"], capture_output=True)
    if storage:
        for line in storage.splitlines():
            if "/data" in line or "/system" in line or "/storage" in line:
                print(line.strip())
    # Network
    print("\n--- Network ---")
    net = run_adb(["shell", "netstat", "-n"], capture_output=True)
    if net:
        lines = net.splitlines()
        for line in lines[:20]:  # first 20 lines
            print(line.strip())
    # CPU info
    print("\n--- CPU ---")
    cpu = run_adb(["shell", "cat", "/proc/cpuinfo"], capture_output=True)
    if cpu:
        for line in cpu.splitlines():
            if "Processor" in line or "Hardware" in line:
                print(line.strip())

def menu_reboot():
    mode = input("Reboot to (system/bootloader/recovery): ").strip().lower()
    if mode == "bootloader":
        run_adb(["reboot", "bootloader"])
    elif mode == "recovery":
        run_adb(["reboot", "recovery"])
    else:
        run_adb(["reboot"])

def menu_wifi():
    choice = input("Enable or disable Wi-Fi? (e/n): ").strip().lower()
    if choice == 'e':
        run_adb(["shell", "svc", "wifi", "enable"])
        print("Wi-Fi enabled.")
    elif choice == 'n':
        run_adb(["shell", "svc", "wifi", "disable"])
        print("Wi-Fi disabled.")
    else:
        print("Invalid choice.")

def menu_battery():
    print("Battery status:")
    out = run_adb(["shell", "dumpsys", "battery"], capture_output=True)
    if out:
        for line in out.splitlines():
            if any(x in line for x in ["level", "status", "health", "temperature", "voltage"]):
                print(line.strip())

# --- NEW SERVICES ---

def menu_extract_phone_numbers():
    """
    Extract phone numbers from contacts database.
    Uses content query or pulls contacts2.db.
    """
    print("Extracting phone numbers from device...")
    # Try to query via content provider (requires permission)
    out = run_adb(["shell", "content", "query", "--uri", "content://contacts/phones", "--projection", "number"], capture_output=True)
    if out and "number" in out:
        numbers = re.findall(r'number=(\+?\d[\d\s\-]+)', out)
        if numbers:
            print("Found phone numbers:")
            for n in set(numbers):
                print(n.strip())
        else:
            print("No numbers found via content query. Trying to pull contacts database...")
            # Alternative: pull contacts2.db
            temp_dir = tempfile.mkdtemp()
            db_path = os.path.join(temp_dir, "contacts.db")
            run_adb(["pull", "/data/data/com.android.providers.contacts/databases/contacts2.db", db_path])
            if os.path.exists(db_path):
                import sqlite3
                conn = sqlite3.connect(db_path)
                c = conn.cursor()
                c.execute("SELECT number FROM raw_contacts JOIN data ON raw_contacts._id=data.raw_contact_id WHERE data.mimetype_id=5")
                rows = c.fetchall()
                if rows:
                    numbers = set(row[0] for row in rows if row[0])
                    print("Found numbers:")
                    for n in numbers:
                        print(n)
                else:
                    print("No numbers found in database.")
                conn.close()
                os.remove(db_path)
                os.rmdir(temp_dir)
            else:
                print("Failed to pull contacts database. Ensure device is rooted or grant permissions.")
    else:
        print("Content query failed. Try pulling database manually using other methods.")

def menu_search_files():
    """
    Search files on device using find/grep.
    """
    search_dir = input("Enter directory to search (e.g., /sdcard): ").strip()
    if not search_dir:
        search_dir = "/sdcard"
    pattern = input("Enter filename pattern or grep string: ").strip()
    if not pattern:
        print("No pattern provided.")
        return
    use_grep = input("Use grep (search inside files) instead of filename? (y/n): ").strip().lower() == 'y'
    if use_grep:
        cmd = f"grep -r '{pattern}' {search_dir} 2>/dev/null | head -50"
    else:
        cmd = f"find {search_dir} -name '*{pattern}*' 2>/dev/null | head -50"
    print(f"Searching... (showing first 50 results)")
    out = run_adb(["shell", cmd], capture_output=True)
    if out:
        print(out)
    else:
        print("No results or error.")

def menu_custom_shell():
    """
    Execute arbitrary shell command.
    """
    cmd = input("Enter shell command to execute: ").strip()
    if cmd:
        print(f"Executing: {cmd}")
        out = run_adb(["shell", cmd], capture_output=True)
        if out:
            print(out)
        else:
            print("Command executed (no output or error).")

def menu_list_apps_details():
    """
    List installed apps with version and path.
    """
    print("Listing installed apps with details...")
    out = run_adb(["shell", "pm", "list", "packages", "-f"], capture_output=True)
    if out:
        lines = out.splitlines()
        # parse format: package:/path/to/apk=package.name
        apps = []
        for line in lines:
            if "=" in line:
                parts = line.split('=')
                if len(parts) == 2:
                    apk_path = parts[0].replace("package:", "")
                    pkg = parts[1]
                    # get version
                    ver = run_adb(["shell", "dumpsys", "package", pkg, "|", "grep", "versionName"], capture_output=True)
                    version = ""
                    if ver:
                        ver_lines = ver.splitlines()
                        for vline in ver_lines:
                            if "versionName" in vline:
                                version = vline.strip().split("=")[-1] if "=" in vline else vline.strip()
                                break
                    apps.append((pkg, version, apk_path))
        if apps:
            print(f"{'Package':<40} {'Version':<20} {'APK Path':<50}")
            print("-"*110)
            for pkg, ver, path in apps:
                print(f"{pkg:<40} {ver:<20} {path:<50}")
        else:
            print("No apps found.")

def menu_logcat():
    """
    Show device logcat (filtered).
    """
    filter_str = input("Enter filter (e.g., *:E or package name, leave blank for all): ").strip()
    lines = input("Number of lines to show (default 50): ").strip()
    lines = int(lines) if lines.isdigit() else 50
    cmd = f"logcat -t {lines}"
    if filter_str:
        cmd += f" | grep -i {filter_str}"
    print(f"Showing last {lines} log lines{' filtered by ' + filter_str if filter_str else ''}")
    out = run_adb(["shell", cmd], capture_output=True)
    if out:
        print(out)
    else:
        print("No logs or error.")

def menu_network_connections():
    """
    Show network connections (netstat).
    """
    out = run_adb(["shell", "netstat", "-an"], capture_output=True)
    if out:
        print("Active connections:")
        print(out)
    else:
        print("No network info.")

def menu_storage_info():
    """
    Detailed storage information.
    """
    print("=== Storage Information ===")
    out = run_adb(["shell", "df", "-h"], capture_output=True)
    if out:
        print(out)
    # Also show disk usage of /data if possible (may take time)
    print("\nTop 10 largest directories in /data (if accessible):")
    out = run_adb(["shell", "du", "-h", "/data", "|", "sort", "-hr", "|", "head", "-10"], capture_output=True)
    if out:
        print(out)

# ----------------------------------------------------------------------
# Main menu
# ----------------------------------------------------------------------

def main_menu():
    while True:
        print("\n" + "="*60)
        print("EasyADB - Interactive ADB Tool (Developer: DangerousAngel)")
        print("="*60)
        print("1.  Pull file/directory")
        print("2.  Push file/directory")
        print("3.  Install APK")
        print("4.  List packages (search pattern)")
        print("5.  Clear app data")
        print("6.  Uninstall app")
        print("7.  Show running processes (ps)")
        print("8.  Force-stop app")
        print("9.  Start activity")
        print("10. Open URL")
        print("11. Set system property")
        print("12. Send broadcast intent")
        print("13. Run-as command")
        print("14. Backup and decrypt package (to tar, optional extract)")
        print("15. Take screenshot")
        print("16. Screen record")
        print("17. Device info (comprehensive)")
        print("18. Reboot device")
        print("19. Enable/disable Wi-Fi")
        print("20. Battery info")
        print("--- NEW SERVICES ---")
        print("21. Extract phone numbers from contacts")
        print("22. Search files on device")
        print("23. Execute custom shell command")
        print("24. List installed apps with details")
        print("25. Show device logs (logcat)")
        print("26. Show network connections")
        print("27. Storage information")
        print("0.  Exit")
        choice = input("Enter your choice: ").strip()

        if choice == '0':
            print("Exiting EasyADB. Goodbye!")
            break
        elif choice == '1':
            menu_pull()
        elif choice == '2':
            menu_push()
        elif choice == '3':
            menu_install()
        elif choice == '4':
            menu_list_packages()
        elif choice == '5':
            menu_clear()
        elif choice == '6':
            menu_uninstall()
        elif choice == '7':
            menu_ps()
        elif choice == '8':
            menu_force_stop()
        elif choice == '9':
            menu_start_activity()
        elif choice == '10':
            menu_open_url()
        elif choice == '11':
            menu_setprop()
        elif choice == '12':
            menu_broadcast()
        elif choice == '13':
            menu_run_as()
        elif choice == '14':
            menu_backup_decrypt()
        elif choice == '15':
            menu_screenshot()
        elif choice == '16':
            menu_screenrecord()
        elif choice == '17':
            menu_device_info()
        elif choice == '18':
            menu_reboot()
        elif choice == '19':
            menu_wifi()
        elif choice == '20':
            menu_battery()
        elif choice == '21':
            menu_extract_phone_numbers()
        elif choice == '22':
            menu_search_files()
        elif choice == '23':
            menu_custom_shell()
        elif choice == '24':
            menu_list_apps_details()
        elif choice == '25':
            menu_logcat()
        elif choice == '26':
            menu_network_connections()
        elif choice == '27':
            menu_storage_info()
        else:
            print("Invalid choice. Please try again.")

        input("\nPress Enter to continue...")

if __name__ == "__main__":
    if not check_adb():
        sys.stderr.write("Error: adb not found in PATH. Please install Android SDK and add adb to PATH.\n")
        sys.exit(1)
    main_menu()