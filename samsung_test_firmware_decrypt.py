import concurrent.futures
import time
import requests
from requests.exceptions import ProxyError, RequestException
import hashlib
import hmac
from lxml import etree
import os
from datetime import datetime
from datetime import timezone
from datetime import timedelta
import json
from copy import deepcopy
from dotenv import load_dotenv
import string
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
import threading
from rich.console import Console
from collections import OrderedDict
import traceback
import argparse
import sys
import multiprocessing

if __name__ == "__main__":
    multiprocessing.set_start_method("fork", force=True)

FORCE_AP = None
FORCE_CSC = None
FORCE_MODEM = None
FORCE_STARTBL = None
FORCE_ENDBL = None
FORCE_SUP = None
FORCE_EUP = None
FORCE_SY = None
FORCE_EY = None
parameters = "not none"
num_workers = os.cpu_count()
BRUTEFORCE = False
FORCE_AP_START = None
FORCE_AP_END = None
FORCE_MODEM_START = None
FORCE_MODEM_END = None
FORCE_MODEL = None

load_dotenv()
thread_local = threading.local()
oldMD5Dict = {}
console = Console(log_path=False)
current_latest_version = "16"  # Current latest Android version number

def printStr(msg):
    console.log(msg)

def getModel():
    ModelDic = {}
    model = args.model
    name = args.model
    modelCode = args.model
    csc = args.csc
    countryCode = []
    for cc in csc.split("|"):
        countryCode.append(cc)
    ModelDic[modelCode] = {"CC": countryCode, "name": name}
    return ModelDic

def getCountryName(cc):
    """
    Get region name by device code
    """
    cc2Country = {
        "CHC": "China",
        "CHN": "China",
        "TGY": "Hong Kong",
        "KOO": "Korea",
        "EUX": "Europe",
        "INS": "India",
        "XAA": "USA",
        "ATT": "USA",
        "TPA": "Panama",
        "ZTO": "Brazil",
        "GTO": "Guatemala",
        "XXV": "Vietnam",
    }
    if cc in cc2Country.keys():
        return cc2Country[cc]
    else:
        return "Unknown Region"


def get_session():
    if not hasattr(thread_local, "session"):
        thread_local.session = requests.Session()
    return thread_local.session


def requestXML(url, max_retries=3, sleep_sec=1):
    """
    Request XML content
    """
    headers = {
        "User-Agent": "SAMSUNG-Android",
        "Accept-Encoding": "identity",
        "Accept": "*/*",
        "Connection": "keep-alive",
    }
    for attempt in range(1, max_retries + 1):
        try:
            session = get_session()
            response = session.get(url, headers=headers, timeout=10)
            response.raise_for_status()
            return response.content
        except ProxyError as e:
            printStr(f"ProxyError({attempt}/{max_retries}): {e}")
        except RequestException as e:
            printStr(f"RequestException({attempt}/{max_retries}): {e}")
        except Exception as e:
            printStr(f"Error occurred ({attempt}/{max_retries}): {e}")
        if attempt < max_retries:
            time.sleep(sleep_sec)
    return None


def readXML_worker(args):
    """XML read task for a single CC"""
    model, cc = args
    md5list = []
    url = f"https://fota-cloud-dn.ospserver.net/firmware/{cc}/{model}/version.test.xml"
    content = requestXML(url)
    if content is not None:
        xml = etree.fromstring(content)
        if len(xml.xpath("//value//text()")) == 0:
            printStr(f"<{model}> Region code <{cc}> input error!!!")
        else:
            for node in xml.xpath("//value//text()"):
                md5list.append(node)
    return cc, md5list


def readXML(model, modelDic):
    """
    Get MD5 values of official website version codes (multi-threaded version)
    """
    md5Dic = {}
    cc_list = modelDic[model]["CC"]
    with ThreadPoolExecutor(max_workers=num_workers) as pool:
        results = pool.map(readXML_worker, [(model, cc) for cc in cc_list])
        for cc, md5list in results:
            if md5list:
                md5Dic[cc] = md5list
    return md5Dic


def _str_range(start: str, end: str) -> list:
    """Generate all strings from start to end (inclusive) over the alphabet 0-9A-Z."""
    letters = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    n = len(start)
    result = []
    def _increment(s):
        chars = list(s)
        for i in range(len(chars) - 1, -1, -1):
            idx = letters.index(chars[i])
            if idx < len(letters) - 1:
                chars[i] = letters[idx + 1]
                for j in range(i + 1, len(chars)):
                    chars[j] = letters[0]
                return "".join(chars)
        return None
    current = start
    while current is not None and current <= end:
        result.append(current)
        if current == end:
            break
        current = _increment(current)
    return result


def char_to_number(char):
    """
    Convert character to corresponding number
    """
    if char.isdigit():
        return int(char)
    elif char.isalpha() and char.isupper():
        return ord(char) - ord("A") + 10
    else:
        raise ValueError("Input must be a character between 0-9 or A-Z")


def get_letters_range(start: str, end: str) -> str:
    """Return string in given range (including end character)"""
    # Get all uppercase letters A-Z
    letters = "0123456789" + string.ascii_uppercase + string.ascii_lowercase
    start_index = letters.find(start)
    end_index = letters.find(end)
    if start_index == -1 or end_index == -1:
        raise ValueError(f"get_letters_range: '{start}' or '{end}' is not in valid character range")
    end_index += 1
    if letters[start_index:end_index] == "":
        raise Exception("String start and end error, please check")
    else:
        return letters[start_index:end_index].upper()


def LoadOldMD5Firmware() -> dict:
    """
    Get previously saved firmware version MD5 information
    Returns:
        Historical MD5 encoded firmware information
    """
    MD5VerFilePath = "md5_encoded_firmware_versions.json"

    try:
        # Ensure file exists, create and write empty dict if not
        if not os.path.isfile(MD5VerFilePath):
            with open(MD5VerFilePath, "w", encoding="utf-8") as file:
                json.dump({}, file)
        # Load JSON data from file
        with open(MD5VerFilePath, "r", encoding="utf-8") as file:
            oldFirmwareJson = json.load(file)
    except json.JSONDecodeError as e:
        # If file content is not valid JSON, return empty dict
        printStr(f"JSON parsing error, error message: {e}")
        oldFirmwareJson = {}

    return oldFirmwareJson


def UpdateOldFirmware(newDict: dict):
    """
    Update historical firmware version MD5 information
    Args:
        newDict(dict): New MD5 encoded firmware version numbers
    """
    global oldMD5Dict
    MD5VerFilePath = "md5_encoded_firmware_versions.json"
    # First read historical data
    if os.path.exists(MD5VerFilePath):
        with open(MD5VerFilePath, "r", encoding="utf-8") as f:
            try:
                old_data = json.load(f)
            except Exception:
                old_data = {}
    else:
        old_data = {}

    # Update historical data
    for k, v in newDict.items():
        old_data[k] = v

    # Save
    with open(MD5VerFilePath, "w", encoding="utf-8") as f:
        f.write(json.dumps(old_data, indent=4, ensure_ascii=False))


def getNowTime() -> str:
    SHA_TZ = timezone(
        timedelta(hours=8),
        name="Asia/Shanghai",
    )
    now = (
        datetime.utcnow()
        .replace(tzinfo=timezone.utc)
        .astimezone(SHA_TZ)
        .strftime("%Y-%m-%d %H:%M")
    )
    return now


def get_next_char(char, alphabet="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"):
    """
    Return next character, return None if does not exist
    """
    index = alphabet.find(char)
    if index == -1:
        return None
    # If not the last character, return next character, otherwise return first character
    return alphabet[(index + 1) % len(alphabet)]


def get_pre_char(char, alphabet="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"):
    """
    Return previous character, return None if does not exist
    """
    index = alphabet.find(char)
    if index == -1:
        return None
    # If not the first character, return previous character, otherwise return last character
    return alphabet[(index - 1) % len(alphabet)]


VERSION_TEST_HMAC_SHA256_KEY = "fcjimts25@%"
MD5_HEX_LENGTH = 32
HMAC_SHA256_HEX_LENGTH = 64


def getVersionHashHmacSHA256(text: str) -> str:
    """
    Compute the HMAC-SHA256 (hex) of a candidate version string using Samsung's
    version.test.xml key. Some devices (e.g. SM-F766U, SM-F966U, SM-A185F) use
    HMAC-SHA256 instead of (or along with) MD5 in version.test.xml.
    """
    return hmac.new(
        VERSION_TEST_HMAC_SHA256_KEY.encode("ascii"),
        text.encode("ascii"),
        hashlib.sha256,
    ).hexdigest()


def matchVersionTestHash(text: str, md5set: set, hmacset: set):
    """
    Check a candidate version string against the MD5 (32 hex) and/or
    HMAC-SHA256 (64 hex) targets read from version.test.xml.
    Returns the matched server hash (to use as dict key) or None.
    """
    if md5set:
        md5hex = hashlib.md5(text.encode("utf-8")).hexdigest()
        if md5hex in md5set:
            return md5hex
    if hmacset:
        hmac256hex = getVersionHashHmacSHA256(text)
        if hmac256hex in hmacset:
            return hmac256hex
    return None


def versionTestHashName(hash_value: str) -> str:
    """
    Return the algorithm name (MD5 or HMAC-SHA256) of a matched server hash.
    """
    return "HMAC-SHA256" if len(hash_value) == HMAC_SHA256_HEX_LENGTH else "MD5"


def _brute_phase1_worker(args):
    chunk, ThirdCode, FirstCode, SecondCode, model, cc, md5set, hmacset, CpVersions_init, oldJson = args
    matches = {}
    new_cp = []
    for i1, bl_version, update_version, yearStr, monthStr in chunk:
        for serialStr in "".join(string.digits[1:] + string.ascii_uppercase):
            randomVersion = bl_version + update_version + yearStr + monthStr + serialStr
            tempCode = "" if not ThirdCode else ThirdCode + i1 + randomVersion
            version1 = FirstCode + i1 + randomVersion + "/" + SecondCode + randomVersion + "/" + tempCode
            matchedHash = matchVersionTestHash(version1, md5set, hmacset)
            if matchedHash:
                matches[matchedHash] = version1
                cp = version1.split("/")[2]
                if cp and cp not in CpVersions_init and cp not in new_cp:
                    new_cp.append(cp)
            vc2 = bl_version + "Z" + yearStr + monthStr + serialStr
            version3 = FirstCode + i1 + vc2 + "/" + SecondCode + vc2 + "/" + tempCode
            if not (model in oldJson and cc in oldJson.get(model, {}) and "versions" in oldJson.get(model, {}).get(cc, {}) and version3 in oldJson[model][cc]["versions"].values()):
                matchedHash = matchVersionTestHash(version3, md5set, hmacset)
                if matchedHash:
                    matches[matchedHash] = version3
                    cp = version3.split("/")[2]
                    if cp and cp not in CpVersions_init and cp not in new_cp:
                        new_cp.append(cp)
    return matches, new_cp


def _brute_phase2_worker(args):
    chunk, ThirdCode, FirstCode, SecondCode, model, cc, md5set, hmacset, CpVersions_full, oldJson = args
    matches = {}
    for i1, bl_version, update_version, yearStr, monthStr in chunk:
        tempCP = CpVersions_full[-12:].copy()
        if ThirdCode:
            for i in range(1, 3):
                initCP = ThirdCode + i1 + bl_version + update_version + yearStr + monthStr + str(i)
                if initCP not in tempCP:
                    tempCP.append(initCP)
        for serialStr in "".join(string.digits[1:] + string.ascii_uppercase):
            initCP1 = ThirdCode + i1 + bl_version + update_version + yearStr + monthStr + get_pre_char(serialStr)
            initCP2 = ThirdCode + i1 + bl_version + update_version + yearStr + monthStr + get_pre_char(get_pre_char(serialStr))
            if initCP1 not in tempCP:
                tempCP.append(initCP1)
            if initCP2 not in tempCP:
                tempCP.append(initCP2)
            randomVersion = bl_version + update_version + yearStr + monthStr + serialStr
            tempCode = "" if not ThirdCode else ThirdCode + i1 + randomVersion
            version1 = FirstCode + i1 + randomVersion + "/" + SecondCode + randomVersion + "/" + tempCode
            for tempCpVersion in tempCP:
                version2 = FirstCode + i1 + randomVersion + "/" + SecondCode + randomVersion + "/" + tempCpVersion
                if version1 == version2:
                    continue
                if (model in oldJson and cc in oldJson.get(model, {}) and "versions" in oldJson.get(model, {}).get(cc, {}) and version2 in oldJson[model][cc]["versions"].values()):
                    continue
                matchedHash = matchVersionTestHash(version2, md5set, hmacset)
                if matchedHash:
                    matches[matchedHash] = version2
            vc2 = bl_version + "Z" + yearStr + monthStr + serialStr
            version3 = FirstCode + i1 + vc2 + "/" + SecondCode + vc2 + "/" + tempCode
            for tempCpVersion in tempCP:
                version4 = FirstCode + i1 + vc2 + "/" + SecondCode + vc2 + "/" + tempCpVersion
                if version1 == version4:
                    continue
                if (model in oldJson and cc in oldJson.get(model, {}) and "versions" in oldJson.get(model, {}).get(cc, {}) and version4 in oldJson[model][cc]["versions"].values()):
                    continue
                matchedHash = matchVersionTestHash(version4, md5set, hmacset)
                if matchedHash:
                    matches[matchedHash] = version4
    return matches


def _run_brute(FirstCode, ThirdCode, SecondCode, model, cc, md5set, hmacset, combos, CpVersions, oldJson, md5list, label=""):
    DecDicts = {}
    prefix = f" [{label}]" if label else ""
    if len(md5list) > 0 and combos:
        _i1, _bl, _up, _yr, _mo = combos[0]
        _rv = _bl + _up + _yr + _mo + "1"
        _tc = "" if not ThirdCode else ThirdCode + _i1 + _rv
        _v1 = FirstCode + _i1 + _rv + "/" + SecondCode + _rv + "/" + _tc
        printStr(f"From prefixes generation example{prefix}: {_v1}")

    if combos:
        chunk_size = max(1, (len(combos) + num_workers - 1) // num_workers)
        chunks = [combos[i:i+chunk_size] for i in range(0, len(combos), chunk_size)]

        shared_args = (ThirdCode, FirstCode, SecondCode, model, cc, md5set, hmacset, list(CpVersions), oldJson)
        with ProcessPoolExecutor(max_workers=num_workers) as pool:
            futures = [pool.submit(_brute_phase1_worker, (chunk, *shared_args)) for chunk in chunks]
            for f in as_completed(futures):
                matches, new_cp = f.result()
                for matchedHash, verStr in matches.items():
                    printStr(f"Added <{model} {getCountryName(cc)}>{prefix} test firmware {versionTestHashName(matchedHash)}: {verStr}")
                DecDicts.update(matches)
                for cp in new_cp:
                    if cp not in CpVersions:
                        CpVersions.append(cp)

        shared_args2 = (ThirdCode, FirstCode, SecondCode, model, cc, md5set, hmacset, list(CpVersions), oldJson)
        with ProcessPoolExecutor(max_workers=num_workers) as pool:
            futures = [pool.submit(_brute_phase2_worker, (chunk, *shared_args2)) for chunk in chunks]
            for f in as_completed(futures):
                matches = f.result()
                for matchedHash, verStr in matches.items():
                    printStr(f"<Baseband> Added <{model} {getCountryName(cc)}>{prefix} test firmware {versionTestHashName(matchedHash)}: {verStr}")
                DecDicts.update(matches)

    return DecDicts


def DecryptionFirmware(
    model: str, md5Dic: dict, cc: str, modelDic: dict, oldJson
) -> dict:
    global parameters
    printStr(
        f"Starting decryption of <{model} {getCountryName(cc)} version> test firmware",
    )
    md5list = md5Dic[cc]
    md5set = {v for v in md5list if len(v) == MD5_HEX_LENGTH}
    hmacset = {v for v in md5list if len(v) == HMAC_SHA256_HEX_LENGTH}
    if md5set and hmacset:
        printStr(
            f"<{model} {getCountryName(cc)}> version.test.xml has both MD5 ({len(md5set)}) and HMAC-SHA256 ({len(hmacset)}) hashes"
        )
    elif hmacset:
        printStr(
            f"<{model} {getCountryName(cc)}> version.test.xml uses HMAC-SHA256 only ({len(hmacset)} hashes)"
        )
    url = f"https://fota-cloud-dn.ospserver.net/firmware/{cc}/{model}/version.xml"
    content = requestXML(url)
    if content == None:
        return None

    ccList = {
        "CHC": ["ZC", "CHC", "ZC"],
        "CHN": ["ZC", "CHC", ""],
        "TGY": ["ZH", "OZS", "ZC"],
        "XAA": ["UE", "OYM", "UE"],
        "KOO": ["KS", "OKR", "KS"],
        "TPA": ["PA", "TPA", "PA"],
        "CPW": ["UB", "OWO", "UB"],
        "BVO": ["UB", "OWO", "UB"],
    }

    try:
        xml = etree.fromstring(content)
        if len(xml.xpath("//latest//text()")) == 0:
            # No official (latest) version published yet for this region/model
            # (version.xml exists but has an empty <latest/> tag).
            latestVer = ""
            latestVerStr = "No official version yet"
            currentOS = "Unknown"

            def code_with(forced, table_val):
                if forced is not None:
                    return model.replace("SM-", "") + forced
                if table_val is not None:
                    return model.replace("SM-", "") + table_val
                return ""

            if cc in ccList.keys():
                prefix = ccList[cc]
            else:
                prefix = (None, None, None)
                if not (FORCE_AP or FORCE_CSC or FORCE_MODEM):
                    printStr(
                        f"Warning: CSC <{cc}> has no official version and no forced "
                        "prefixes (--ap/--cscp/--modem) were given. "
                        "Nothing can be matched for this region."
                    )
            FirstCode = code_with(FORCE_AP, prefix[0])
            SecondCode = code_with(FORCE_CSC, prefix[1])
            ThirdCode = code_with(FORCE_MODEM, prefix[2])

            if cc in ccList.keys():
                startYear = chr(datetime.now().year - 2001 - 5 + ord("A"))
                endYear = "Z"
            else:
                startYear = chr(datetime.now().year - 2001 - 1 + ord("A"))
                endYear = get_next_char(startYear) or startYear
        else:
            # Directly get current latest version number information from server
            latestVerStr = xml.xpath("//latest//text()")[0]
            latestVer = latestVerStr.split("/")
            currentOS = xml.xpath("//latest//@o")[0]

            FirstCode = latestVer[0][:-6]
            SecondCode = latestVer[1][:-5]
            ThirdCode = latestVer[2][:-6]

            if FORCE_AP is not None:
                FirstCode = model.replace("SM-", "") + FORCE_AP
            if FORCE_CSC is not None:
                SecondCode = model.replace("SM-", "") + FORCE_CSC
            if FORCE_MODEM is not None:
                ThirdCode = model.replace("SM-", "") + FORCE_MODEM
                parameters = None

            if cc in ccList and parameters is not None:
                FirstCode = model.replace("SM-", "") + ccList[cc][0]
                SecondCode = model.replace("SM-", "") + ccList[cc][1]
                ThirdCode = model.replace("SM-", "") + ccList[cc][2]
                printStr(f"Using custom cclist prefixes: {cc}: {FirstCode}, {SecondCode}, {ThirdCode}")

            startYear = chr(
                datetime.now().year - 2001 - 4 + ord("A")
            )

        Dicts = {model: {cc: {"versions": {}, "latest_test_upload_time": ""}}}
        DecDicts = {}
        oldDicts = {model: {cc: {}}}
        CpVersions = []

        lastVersion1 = ""
        lastVersion2 = ""

        if (
            model in oldJson
            and cc in oldJson[model]
            and "regular_update_test" in oldJson[model][cc]
        ):
            if "None" in oldJson[model][cc]["major_version_test"].split("/")[0]:
                lastVersion1 = oldJson[model][cc]["regular_update_test"].split("/")[0]
            else:
                lastVersion1 = oldJson[model][cc]["regular_update_test"].split("/")[0]
                lastVersion2 = oldJson[model][cc]["major_version_test"].split("/")[0]
            oldDicts[model][cc] = deepcopy(oldJson[model][cc]["versions"])
            seen = set()
            modelVersion = [
                x.split("/")[-1] for x in oldJson[model][cc]["versions"].values()
            ]
            newMV = [x for x in modelVersion if not (x in seen or seen.add(x))][-12:]
            CpVersions = newMV

        startUpdateCount = "A"
        endUpdateCount = "B"
        startBLVersion = "0"
        endBLVersion = "2"

        if lastVersion1:
            startBLVersion = lastVersion1[-5]
            if latestVer:
                startUpdateCount = latestVer[0][-4]
            startYear = lastVersion1[-3]

        if latestVer:
            endBLVersion = get_next_char(latestVer[0][-5])
            endUpdateCount = get_next_char(latestVer[0][-4])
            if latestVer[0][-2] in "JKL":
                endYear = get_next_char(latestVer[0][-3])
            else:
                endYear = latestVer[0][-3]

        alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"

        def ensure_char(c, default):
            if c is None or len(c) != 1 or c not in alphabet:
                return default
            return c

        all_forced = (
            FORCE_STARTBL is not None and FORCE_ENDBL is not None
            and FORCE_SUP is not None and FORCE_EUP is not None
            and FORCE_SY is not None and FORCE_EY is not None
        )
        if all_forced:
            startBLVersion = FORCE_STARTBL
            endBLVersion = FORCE_ENDBL
            startUpdateCount = FORCE_SUP
            endUpdateCount = FORCE_EUP
            startYear = FORCE_SY
            endYear = FORCE_EY
        else:
            print("")
            print("           Some parameters are missing! Running in simple mode.")
            print("")
            
        startBLVersion = ensure_char(startBLVersion, "0")
        endBLVersion = ensure_char(endBLVersion, "2")
        startUpdateCount = ensure_char(startUpdateCount, "A")
        endUpdateCount = ensure_char(endUpdateCount, "B")
        startYear = ensure_char(startYear, chr(datetime.now().year - 2001 - 1 + ord('A')))
        endYear = ensure_char(endYear, get_next_char(startYear) or startYear)
        
        def fix_order(a, b):
            if alphabet.index(a) > alphabet.index(b):
                return b, a
            return a, b

        startBLVersion, endBLVersion = fix_order(startBLVersion, endBLVersion)
        startUpdateCount, endUpdateCount = fix_order(startUpdateCount, endUpdateCount)
        startYear, endYear = fix_order(startYear, endYear)

        updateLst = get_letters_range(startUpdateCount, endUpdateCount)
        updateLst += "Z"

        starttime = time.perf_counter()

        combos = []
        for i1 in "US":
            for bl_version in get_letters_range(startBLVersion, endBLVersion):
                for update_version in updateLst:
                    for yearStr in get_letters_range(startYear, endYear):
                        for monthStr in get_letters_range("A", "L"):
                            combos.append((i1, bl_version, update_version, yearStr, monthStr))

        CpVersions_initial = list(CpVersions)
        result = _run_brute(FirstCode, ThirdCode, SecondCode, model, cc, md5set, hmacset, combos, CpVersions, oldJson, md5list)
        DecDicts.update(result)

        if FORCE_MODEL:
            matched = set(DecDicts.keys())
            remain_md5 = md5set - matched
            remain_hmac = hmacset - matched
            if remain_md5 or remain_hmac:
                remain_list = list(remain_md5 | remain_hmac)
                xml_model_prefix = model.replace("SM-", "")
                fm_prefix = FORCE_MODEL.replace("SM-", "")
                fm_FirstCode = fm_prefix + FirstCode[len(xml_model_prefix):]
                fm_SecondCode = fm_prefix + SecondCode[len(xml_model_prefix):]
                fm_ThirdCode = fm_prefix + ThirdCode[len(xml_model_prefix):]
                CpVersions = list(CpVersions_initial)
                printStr(f"Force-model: retrying with {FORCE_MODEL} ({len(remain_list)} hash(es) remaining)")
                result = _run_brute(fm_FirstCode, fm_ThirdCode, fm_SecondCode, model, cc, remain_md5, remain_hmac, combos, CpVersions, oldJson, remain_list, label=f"force-{FORCE_MODEL}")
                DecDicts.update(result)
            else:
                printStr(f"Force-model: all hashes decrypted on first try, skipping {FORCE_MODEL} retry")

        if BRUTEFORCE:
            matched = set(DecDicts.keys())
            remain_md5 = md5set - matched
            remain_hmac = hmacset - matched
            if remain_md5 or remain_hmac:
                remain_list = list(remain_md5 | remain_hmac)
                ap_range = _str_range(FORCE_AP_START, FORCE_AP_END)
                modem_range = _str_range(FORCE_MODEM_START, FORCE_MODEM_END)
                model_prefix = model.replace("SM-", "")
                for ap in ap_range:
                    for modem in modem_range:
                        bf_FirstCode = model_prefix + ap
                        bf_ThirdCode = model_prefix + modem
                        CpVersions = list(CpVersions_initial)
                        printStr(f"Brute-force: AP={ap}, Modem={modem} ({len(remain_list)} hash(es) remaining)")
                        result = _run_brute(bf_FirstCode, bf_ThirdCode, SecondCode, model, cc, remain_md5, remain_hmac, combos, CpVersions, oldJson, remain_list, label=f"{ap}/{modem}")
                        DecDicts.update(result)
                        remain_md5 -= set(result.keys())
                        remain_hmac -= set(result.keys())
                        remain_list = list(remain_md5 | remain_hmac)
                        if not remain_list:
                            break
                    if not remain_list:
                        break
                if remain_list:
                    printStr(f"Brute-force: {len(remain_list)} hash(es) still undecrypted after all AP/modem combinations")
            else:
                printStr("Brute-force: all hashes decrypted on first try, skipping AP/modem range scan")

        oldDicts[model][cc].update(DecDicts)
        key_func = make_sort_key(oldDicts[model][cc].values())
        sortedList = sorted(oldDicts[model][cc].values(), key=key_func)

        if latestVerStr != "No official version yet" and latestVerStr:
            stableVersion = latestVerStr.split("/")[0]
            currentChar = stableVersion[-4]
            majorChar = get_next_char(stableVersion[-4])
            minorVersion = getLatestVersion(sortedList, currentChar)
            if minorVersion is None:
                minorVersion = "No test firmware found"
            majorVerison = getLatestVersion(sortedList, majorChar)
            if majorVerison is None:
                majorVerison = "No major version test yet"
            else:
                majorChar = get_next_char(stableVersion[-4]) + "Z"
                majorVerison = getLatestVersion(sortedList, majorChar)
            Dicts[model][cc]["regular_update_test"] = minorVersion
            Dicts[model][cc]["major_version_test"] = majorVerison
        else:
            if sortedList:
                Dicts[model][cc]["regular_update_test"] = sortedList[-1]
            else:
                Dicts[model][cc]["regular_update_test"] = "No test firmware found"
            Dicts[model][cc]["major_version_test"] = "No major version test yet"

        Dicts[model][cc]["versions"] = DecDicts
        Dicts[model][cc]["latest_test_upload_time"] = ""
        if DecDicts:
            new_latest1 = Dicts[model][cc]["regular_update_test"].split("/")[0]
            new_latest2 = Dicts[model][cc]["major_version_test"].split("/")[0]
            if new_latest1 != lastVersion1 or new_latest2 != lastVersion2:
                Dicts[model][cc]["latest_test_upload_time"] = getNowTime()
        Dicts[model][cc]["latest_official"] = latestVerStr
        Dicts[model][cc]["official_android_version"] = currentOS

        if currentOS != "Unknown":
            if Dicts[model][cc]["major_version_test"].split("/")[0][-4] == "Z":
                Dicts[model][cc]["test_android_version"] = str(int(currentOS) + 1)
            else:
                if 'None' in Dicts[model][cc]["major_version_test"].split("/")[0]:
                    Dicts[model][cc]["test_android_version"] = str(
                        int(currentOS)
                        + ord(Dicts[model][cc]["regular_update_test"].split("/")[0][-4])
                        - ord(Dicts[model][cc]["latest_official"].split("/")[0][-4])
                    )
                else:
                    Dicts[model][cc]["test_android_version"] = str(
                        int(currentOS)
                        + ord(Dicts[model][cc]["major_version_test"].split("/")[0][-4])
                        - ord(Dicts[model][cc]["latest_official"].split("/")[0][-4])
                    )
        else:
            Dicts[model][cc]["official_android_version"] = current_latest_version
            Dicts[model][cc]["test_android_version"] = current_latest_version

        endtime = time.perf_counter()
        if (
            model in oldJson
            and cc in oldJson[model]
            and "versions" in oldJson[model][cc]
            and oldJson[model][cc]["versions"]
        ):
            sumCount = len(Dicts[model][cc]["versions"]) + len(oldJson[model][cc]["versions"])
            rateOfSuccess = round(sumCount / len(md5list) * 100, 2)
        else:
            rateOfSuccess = round(len(Dicts[model][cc]["versions"]) / len(md5list) * 100, 2)
        Dicts[model][cc]["decryption_percentage"] = f"{rateOfSuccess}%"
        printStr(
            f"<{modelDic[model]['name']} {getCountryName(cc)} version> decryption completed, time: {round(endtime - starttime, 2)}s, success: {rateOfSuccess}%"
        )
        if DecDicts:
            printStr(f"Added {len(DecDicts)} test firmware(s).")
        return Dicts
    except Exception as e:
        printStr(f"Error occurred: {e}")
        traceback.print_exc()
        return None

def make_sort_key(strings):
    order = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    order_map = {c: i for i, c in enumerate(order)}

    def get_tail4(s):
        first_part = s.split("/")[0]
        return first_part[-4:] if len(first_part) >= 4 else first_part

    def key_func(s):
        tail4 = get_tail4(s)
        if len(tail4) < 4:
            return (-1, -1, -1, -1)
        last3 = tail4[-3:]
        fourth = tail4[-4]
        z_priority = 0 if fourth == "Z" else 1
        return tuple(order_map.get(c, 98) for c in last3) + (
            z_priority,
            order_map.get(fourth, 98),
        )

    return key_func


def getLatestVersion(version_list, chars):
    """
    Filter version numbers where the 4th character from the end is in the specified character set, sort by last 3 characters in ascending order, and return the maximum version number.
    :param version_list: List of version number strings
    :param chars: Specified character set for the 4th character from the end (e.g. "ZAB")
    :return: Maximum version number string (None if not found)
    """
    order = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    order_map = {c: i for i, c in enumerate(order)}

    def get_tail4(s):
        first_part = s.split("/")[0]
        return first_part[-4:] if len(first_part) >= 4 else first_part

    # Support filtering by multiple characters
    filtered = [
        s for s in version_list if len(get_tail4(s)) == 4 and get_tail4(s)[0] in chars
    ]
    if not filtered:
        return None

    def last3_key(s):
        tail4 = get_tail4(s)
        return tuple(order_map.get(c, -1) for c in tail4[1:])

    return max(filtered, key=last3_key)

def run():
    # Get related parameter variable data
    global args
    global modelDic, oldMD5Dict
    jsonStr = ""
    decDicts = {"last_update_time": getNowTime()}
    if args.output:
        VerFilePath = f"{args.output}.json"
        Ver_mini_FilePath = f"{args.output}_mini.json"
    else:
        VerFilePath = "firmware.json"
        Ver_mini_FilePath = "firmware_mini.json"
    startTime = time.perf_counter()
    if not os.path.exists(VerFilePath):
        with open(VerFilePath, "w") as file:
            file.write("{}")

    with open(VerFilePath, "r", encoding="utf-8") as f:
        jsonStr = f.read()
        oldJson = {}
        if jsonStr != "":
            oldJson = json.loads(jsonStr)
        with ProcessPoolExecutor(max_workers=num_workers) as pool:
            future_to_model = {
                pool.submit(getNewVersions, oldJson, model, modelDic, oldMD5Dict): model
                for model in modelDic
            }
            for future in concurrent.futures.as_completed(future_to_model):
                model = future_to_model[future]
                result = future.result()
                if result is not None:
                    _, newMDic = result
                    for m, cc_dict in newMDic.items():
                        if m not in decDicts:
                            decDicts[m] = {}
                        for cc, cc_data in cc_dict.items():
                            decDicts[m][cc] = cc_data

    endTime = time.perf_counter()
    printStr(f"Total time: {round(endTime - startTime, 2)}s")
    # Create deep copy to avoid destroying original data
    firmware_info_mini = deepcopy(decDicts)
    for model_data in firmware_info_mini.values():
        if isinstance(model_data, dict):
            for region_data in model_data.values():
                if isinstance(region_data, dict):
                    region_data.pop("versions", None)
    sorted_firmware_info_mini = OrderedDict()
    for model in sorted(firmware_info_mini.keys()):
        sorted_firmware_info_mini[model] = firmware_info_mini[model]
    with open(Ver_mini_FilePath, "w", encoding="utf-8") as f:
        f.write(json.dumps(sorted_firmware_info_mini, indent=4, ensure_ascii=False))
    # Before writing firmware.json, sort version numbers for each model/region
    for model in decDicts:
        if model == "last_update_time":
            continue
        for region in decDicts[model]:
            if "versions" in decDicts[model][region]:
                ver_dict = decDicts[model][region]["versions"]
                # Get all values
                values = list(ver_dict.values())
                # Generate sort key
                key_func = make_sort_key(values)
                # Sort by value and rebuild dictionary
                sorted_items = sorted(
                    ver_dict.items(), key=lambda item: key_func(item[1])
                )
                decDicts[model][region]["versions"] = dict(sorted_items)
    sorted_decDicts = OrderedDict()
    for model in sorted(decDicts.keys()):
        sorted_decDicts[model] = decDicts[model]
    with open(VerFilePath, "w", encoding="utf-8") as f:
        f.write(json.dumps(sorted_decDicts, indent=4, ensure_ascii=False))


def process_cc(cc, modelDic, oldMD5Dict, md5Dic, oldJson, model):
    newMDic = {model: {}}
    newMD5Dict = {model: {}}
    hasNewVersion = False
    if model in oldJson.keys() and cc in oldJson[model].keys():
        # Copy existing device firmware version content
        newMDic[model][cc] = deepcopy(oldJson[model][cc])
        # Initialize if following keys don't exist
        newMDic[model][cc].setdefault("latest_test_upload_time", "None")
        newMDic[model][cc].setdefault("official_android_version", "")
        newMDic[model][cc].setdefault("test_android_version", "")
    else:
        # Initialize content for new device
        newMDic[model][cc] = {
            "versions": {},
            "major_version_test": "",
            "latest_official": "",
            "latest_version_description": "",
            "decryption_percentage": "",
            "latest_test_upload_time": "None",
            "official_android_version": "",
            "test_android_version": "",
            "region": "",
            "model": "",
            "decryption_count": 0,
        }
    if model in oldMD5Dict and cc in oldMD5Dict[model]:
        newMD5Dict[model][cc] = deepcopy(oldMD5Dict[model][cc])
    else:
        # Initialize content for new device
        newMD5Dict[model][cc] = {"versions": {}, "firmware_count": 0}
    newMD5Dict[model][cc]["versions"] = md5Dic[cc]
    newMD5Dict[model][cc]["firmware_count"] = len(md5Dic[cc])

    verDic = DecryptionFirmware(model, md5Dic, cc, modelDic, oldJson)  # Decrypt to get new data
    if verDic is None or model not in verDic or cc not in verDic[model] or "versions" not in verDic[model][cc]:
        return False, {}, {}
    newMDic[model][cc]["latest_official"] = verDic[model][cc]["latest_official"]

    newMDic[model][cc]["region"] = getCountryName(cc)
    newMDic[model][cc]["model"] = modelDic[model]["name"]
    if verDic[model][cc]["major_version_test"] != "":
        newMDic[model][cc]["major_version_test"] = verDic[model][cc]["major_version_test"]
    if verDic[model][cc]["regular_update_test"] != "":
        newMDic[model][cc]["regular_update_test"] = verDic[model][cc]["regular_update_test"]
    if verDic[model][cc]["latest_official"] != "":
        newMDic[model][cc]["latest_official"] = verDic[model][cc]["latest_official"]
    if verDic[model][cc]["latest_test_upload_time"] != "":
        newMDic[model][cc]["latest_test_upload_time"] = verDic[model][cc][
            "latest_test_upload_time"
        ]
    newMDic[model][cc]["official_android_version"] = verDic[model][cc]["official_android_version"]
    newMDic[model][cc]["test_android_version"] = verDic[model][cc]["test_android_version"]

    # Version number description
    ver = newMDic[model][cc]["major_version_test"].split("/")[0]
    ver2 = newMDic[model][cc]["regular_update_test"].split("/")[0]
    
    def is_valid_version_string(s):
        return s and len(s) >= 4 and all(c in "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" for c in s[-4:])
    
    if is_valid_version_string(ver):
        yearStr = ord(ver[-3]) - 65 + 2001
        monthStr = ord(ver[-2]) - 64
        countStr = char_to_number(ver[-1])
        definitionStr = f"Year {yearStr} Month {monthStr} #{countStr} major version test"
        newMDic[model][cc]["latest_version_description"] = definitionStr
    elif is_valid_version_string(ver2):
        yearStr = ord(ver2[-3]) - 65 + 2001
        monthStr = ord(ver2[-2]) - 64
        countStr = char_to_number(ver2[-1])
        definitionStr = f"Year {yearStr} Month {monthStr} #{countStr} regular update test"
        newMDic[model][cc]["latest_version_description"] = definitionStr
    else:
        newMDic[model][cc]["latest_version_description"] = "None"
    
    if verDic[model][cc]["decryption_percentage"] != "":
        newMDic[model][cc]["decryption_percentage"] = verDic[model][cc]["decryption_percentage"]
    
    if len(verDic[model][cc]["versions"]) == 0:
        return False, newMDic, newMD5Dict
    
    diffModel = set(verDic[model][cc]["versions"].keys()) - set(
        newMDic[model][cc]["versions"].keys()
    )
    if diffModel:
        hasNewVersion = True
        for key in diffModel:
            newMDic[model][cc]["versions"][key] = verDic[model][cc]["versions"][key]
    
    newMDic[model][cc]["versions"] = dict(
        sorted(
            newMDic[model][cc]["versions"].items(), key=lambda x: x[1].split("/")[0][-3:]
        )
    )
    newMDic[model][cc]["decryption_count"] = len(newMDic[model][cc]["versions"])
    return hasNewVersion, newMDic, newMD5Dict


def getNewVersions(oldJson, model, modelDic, oldMD5Dict):
    md5Dic = readXML(model, modelDic)  # Return md5 dictionary containing multiple regional versions
    if len(md5Dic) == 0:
        return
    newMDic = {model: {}}
    md5Dicts_list = []  # Used to collect newMD5Dict from each thread
    hasNewVersion = False
    with ProcessPoolExecutor(max_workers=num_workers) as pool:
        future_to_cc = {
            pool.submit(
                process_cc, cc, modelDic, oldMD5Dict, md5Dic, oldJson, model
            ): cc
            for cc in md5Dic.keys()
        }
        for future in as_completed(future_to_cc):
            result = future.result()
            if result is None:
                continue
            hasNew, newMDic_part, newMD5Dict_part = result
            if hasNew:
                hasNewVersion = True
            for m, cc_dict in newMDic_part.items():
                if m not in newMDic:
                    newMDic[m] = {}
                for cc, cc_data in cc_dict.items():
                    newMDic[m][cc] = cc_data
            md5Dicts_list.append(newMD5Dict_part)
    # Merge newMD5Dict
    mergedMD5Dict = {"last_update_time": getNowTime()}
    mergedMD5Dict[model] = {}
    for md5Dict in md5Dicts_list:
        if model in md5Dict:
            mergedMD5Dict[model].update(md5Dict[model])
    UpdateOldFirmware(mergedMD5Dict)  # Update historical firmware Json information
    return hasNewVersion, newMDic


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Decrypt Samsung firmware test versions.')
    parser.add_argument('--ap', help='Force AP prefix (e.g., UB)')
    parser.add_argument('--cscp', help='Force CSC prefix (e.g., OWO)')
    parser.add_argument('--modem', help='Force modem prefix (e.g., UB)')
    parser.add_argument('--bls', help='Bootloader SW Rev Bit start (e.g., 7)')
    parser.add_argument('--ble', help='Bootloader SW Rev Bit end (e.g., 9)')
    parser.add_argument('--sup', help='Major update version start (e.g., A)')
    parser.add_argument('--eup', help='Major update version end (e.g., E)')
    parser.add_argument('--sy', help='Scan start year (e.g., W)')
    parser.add_argument('--ey', help='Scan end year (e.g., Y)')
    parser.add_argument('--output', help='Base name for output files (without extension)')
    parser.add_argument('--model', help='Model name (e.g., SM-A156M)')
    parser.add_argument('--csc', help='Country Service Code (e.g, ZTO)')
    parser.add_argument('--workers', type=int, default=os.cpu_count(), help='Number of parallel workers (default: CPU count)')
    parser.add_argument('--bruteforce', action='store_true', help='Enable AP/modem range brute-force')
    parser.add_argument('--ap-start', help='AP range start (e.g., AA)')
    parser.add_argument('--ap-end', help='AP range end (e.g., AZ)')
    parser.add_argument('--modem-start', help='Modem range start (e.g., AA)')
    parser.add_argument('--modem-end', help='Modem range end (e.g., AZ)')
    parser.add_argument('--force-model', help='Override model for version string construction (e.g., SM-A185F)')
    args = parser.parse_args()
    
    if args.ap:
        FORCE_AP = args.ap
    if args.cscp:
        FORCE_CSC = args.cscp
    if args.modem:
        FORCE_MODEM = args.modem
    if args.bls:
        FORCE_STARTBL = args.bls
    if args.ble:
        FORCE_ENDBL = args.ble
    if args.sup:
        FORCE_SUP = args.sup
    if args.eup:
        FORCE_EUP = args.eup        # Major version from A to Z
    if args.sy:
        FORCE_SY = args.sy
    if args.ey:
        FORCE_EY = args.ey
    if args.workers:
        num_workers = args.workers
    if args.bruteforce:
        BRUTEFORCE = True
        if args.ap_start:
            FORCE_AP_START = args.ap_start
        if args.ap_end:
            FORCE_AP_END = args.ap_end
        if args.modem_start:
            FORCE_MODEM_START = args.modem_start
        if args.modem_end:
            FORCE_MODEM_END = args.modem_end
    if args.force_model:
        FORCE_MODEL = args.force_model

    if args.model and args.csc is None:
        sys.exit("Error: Critical parameters missing.")

    if BRUTEFORCE and (not FORCE_AP_START or not FORCE_AP_END or not FORCE_MODEM_START or not FORCE_MODEM_END):
        sys.exit("Error: --bruteforce requires --ap-start, --ap-end, --modem-start, --modem-end.")

    try:
        oldMD5Dict = LoadOldMD5Firmware()  # Get last MD5 encoded version number data
        try:
            modelDic = getModel()  # Get model information from arguments
        except Exception:
            sys.exit("Error: Something went wrong.")
        run()
    except Exception as e:
        printStr(f"Error occurred: {e}")
