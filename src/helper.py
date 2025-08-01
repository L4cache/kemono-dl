import re
import hashlib
import os
import time
import requests
from urllib.parse import urlparse, urlencode, parse_qs, urlunparse

from .args import get_args
from .logger import logger

running_args = get_args()

def parse_url(url):
    # parse urls
    downloadable = re.search(r'^https://((?:kemono|coomer)\.(?:party|su|cr|st))/([^/]+)/user/([^/]+)($|/post/([^/]+))($|/revision/([^/]+)$)',url)
    if not downloadable:
        return None
    return downloadable.group(1)

# create path from template pattern
def compile_post_path(post_variables, template, ascii):
    drive, tail = os.path.splitdrive(template)
    tail_trimmed = tail[0] in {'/','\\'}
    tail = tail[1:] if tail_trimmed else tail
    tail_split = re.split(r'\\|/', tail)
    cleaned_path = (drive + os.path.sep if drive else 
                    (os.path.sep if tail_trimmed else ''))
    for folder in tail_split:
        if ascii:
            cleaned_path = os.path.join(cleaned_path, restrict_ascii(clean_folder_name(folder.format(**post_variables))))
        else:
            cleaned_path = os.path.join(cleaned_path, clean_folder_name(folder.format(**post_variables)))
    return cleaned_path

# create file path from template pattern
def compile_file_path(post_path, post_variables, file_variables, template, ascii):
    file_split = re.split(r'\\|/', template)
    if len(file_split) > 1:
        for folder in file_split[:-1]:
            if ascii:
                post_path = os.path.join(post_path, restrict_ascii(clean_folder_name(folder.format(**file_variables, **post_variables))))
            else:
                post_path = os.path.join(post_path, clean_folder_name(folder.format(**file_variables, **post_variables)))
    if ascii:
        cleaned_file = restrict_ascii(clean_file_name(file_split[-1].format(**file_variables, **post_variables)))
    else:
        cleaned_file = clean_file_name(file_split[-1].format(**file_variables, **post_variables))
    return os.path.join(post_path, cleaned_file)

# get file hash
def get_file_hash(file:str,blksize:int=4<<20):
    sha256_hash = hashlib.sha256()
    with open(file,"rb") as f:
        for byte_block in iter(lambda: f.read(blksize),b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest().lower()

# clean folder name for windows & linux
def clean_folder_name(folder_name:str):
    if not folder_name.rstrip():
        folder_name = '_'
    name_clean = re.sub(r'[\x00-\x1f\\/:\"*?<>\|]|\.$','_',folder_name.rstrip())[:248]
    while len(name_clean.encode('utf-8','replace')) > 255: # filename length limit: windows is 255 *characters*, linux is 255 *bytes* unless you are HACKERMAN and hacked the kernel
        name_clean = name_clean[:-1]
    return name_clean

# clean file name for windows & linux
def clean_file_name(file_name:str):
    if not file_name:
        file_name = '_'
    file_name = re.sub(r'[\x00-\x1f\\/:\"*?<>\|]','_', file_name)
    file_name, file_extension = os.path.splitext(file_name)
    name_limit = 255-len(file_extension)-5
    name_clean = file_name[:name_limit] + file_extension
    while len(name_clean.encode('utf-8','replace')) > 250: # same thing, minus 5 for .part extension added in downloading file
        name_limit -= 1
        name_clean = file_name[:name_limit] + file_extension
    return name_clean

def restrict_ascii(string:str):
    return re.sub(r'[^\x21-\x7f]','_',string)

def check_date(post_date, date, datebefore, dateafter):
    if date:
        if date == post_date:
            return 0
        elif date > post_date:
            return 2
    if datebefore and dateafter:
        if dateafter <= post_date <= datebefore:
            return 0
        elif dateafter > post_date:
            return 2
    elif datebefore:
        if datebefore >= post_date:
            return 0
    elif dateafter:
        if dateafter <= post_date:
            return 0
        else:
            return 2
    return 1

# prints download bar
def print_download_bar(total:int, downloaded:int, resumed:int, start):
    time_diff = time.time() - start
    if time_diff == 0.0:
        time_diff = 0.000001
    done = 50

    rate = (downloaded-resumed)/time_diff

    eta = time.strftime("%H:%M:%S", time.gmtime((total-downloaded) / rate)) if rate else '99:99:99'

    if rate/2**10 < 100:
        rate = (round(rate/2**10, 1), 'KB')
    elif rate/2**20 < 100:
        rate = (round(rate/2**20, 1), 'MB')
    else:
        rate = (round(rate/2**30, 1), 'GB')

    if total:
        done = int(50*downloaded/total)
        if total/2**10 < 100:
            total = (round(total/2**10, 1), 'KB')
            downloaded = round(downloaded/2**10,1)
        elif total/2**20 < 100:
            total = (round(total/2**20, 1), 'MB')
            downloaded = round(downloaded/2**20,1)
        else:
            total = (round(total/2**30, 1), 'GB')
            downloaded = round(downloaded/2**30,1)
    else:
        if downloaded/2**10 < 100:
            total = ('???', 'KB')
            downloaded = round(downloaded/2**10,1)
        elif downloaded/2**20 < 100:
            total = ('???', 'MB')
            downloaded = round(downloaded/2**20,1)
        else:
            total = ('???', 'GB')
            downloaded = round(downloaded/2**30,1)

    bar_fill = '='*done
    bar_empty = ' '*(50-done)
    overlap_buffer = ' '*15
    print(f'[{bar_fill}{bar_empty}] {downloaded}/{total[0]} {total[1]} at {rate[0]} {rate[1]}/s ETA {eta}{overlap_buffer}', end='\r')

# redo this
# def check_version():
#     try:
#         current_version = datetime.datetime.strptime(__version__, r'%Y.%m.%d')
#     except:
#         current_version = datetime.datetime.strptime(__version__, r'%Y.%m.%d.%H')
#     github_api_url = 'https://api.github.com/repos/AplhaSlayer1964/kemono-dl/releases/latest'
#     try:
#         latest_tag = requests.get(url=github_api_url, timeout=300).json()['tag_name']
#     except:
#         logger.error("Failed to check latest version of kemono-dl")
#         return
#     try:
#         latest_version = datetime.datetime.strptime(latest_tag, r'%Y.%m.%d')
#     except:
#         latest_version = datetime.datetime.strptime(latest_tag, r'%Y.%m.%d.%H')
#     if current_version < latest_version:
#         logger.debug(f"Using kemono-dl {__version__} while latest release is kemono-dl {latest_tag}")
#         logger.warning(f"A newer version of kemono-dl is available. Please update to the latest release at https://github.com/AplhaSlayer1964/kemono-dl/releases/latest")


# doesn't support multithreading
def function_rate_limit(func):
    last_call_times = {}

    def wrapper(*args, **kwargs):
        nonlocal last_call_times
        func_name = func.__name__
        t = time.time()
        last_call_time = last_call_times.get(func_name, 0)
        if (t - last_call_time) * 1000 < running_args['ratelimit_ms']:
            time.sleep(running_args['ratelimit_ms'] / 1000 - (t - last_call_time))
        last_call_times[func_name] = time.time()
        return func(*args, **kwargs)

    return wrapper

class RefererSession(requests.Session):
    def __init__(self, *args, **kwargs):
        self.proxy_agent = kwargs.pop('proxy_agent', None)
        self.max_retries_429 = kwargs.pop('max_retries_429', 3)
        self.sleep_429 = kwargs.pop('sleep_429', 120)

        super().__init__(*args, **kwargs)

    def rebuild_auth(self, prepared_request, response):
        super().rebuild_auth(prepared_request, response)
        u = urlparse(response.url)
        prepared_request.headers["Referer"] = f'{u.scheme}://{u.netloc}/'

    @function_rate_limit
    def get(self, url, **kwargs):
        old_url = url
        retry_429 = kwargs.pop('retry_429', True)
        max_retries_429 = kwargs.pop('max_retries_429', self.max_retries_429)
        
        if self.proxy_agent:
            u = urlparse(self.proxy_agent)
            q_params = parse_qs(u.query)
            q_params['u'] = url
            u = u._replace(query=urlencode(q_params))
            url = urlunparse(u)

        resp = super().get(url, **kwargs)
        max_retries_429 -= 1
        if resp.status_code != 429 or not retry_429 or max_retries_429 < 1:
            return resp

        # need retry
        logger.warning(f"Failed to access: {url if self.proxy_agent else old_url} | {resp.status_code} Too Many Requests | Sleeping for {self.sleep_429} seconds")
        time.sleep(self.sleep_429)
        return self.get(old_url, retry_429=retry_429, max_retries_429=max_retries_429, **kwargs)