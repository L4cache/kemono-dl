import requests
from requests.adapters import HTTPAdapter, Retry
import re
import os
from bs4 import BeautifulSoup
import time
import datetime
from PIL import Image
from io import BytesIO
import json
from numbers import Number
import pathlib
import itertools
import zipfile
import py7zr
import rarfile
import shutil
import hashlib

from .args import get_args
from .logger import logger
from .version import __version__
from .helper import get_file_hash, print_download_bar, check_date, parse_url, compile_post_path, compile_file_path, RefererSession
# from .my_yt_dlp import my_yt_dlp

class downloader:

    def __init__(self, args):
        self.input_urls = args['links'] + args['from_file']
        if args['cccp']:
            self.input_urls = [i.replace('.party','.su') for i in self.input_urls]
        # list of completed posts from current session
        self.comp_posts = []
        # list of creators info
        self.creators = []

        # requests variables
        self.headers = {'User-Agent': args['user_agent']} if args['user_agent'] else {}
        self.cookies = args['cookies']
        self.timeout = 300

        self.headcheck = args['head_check']

        for i in ('/v1','/v0'):
            self.api_ver = i
            if requests.get(f'https://kemono.su/api{self.api_ver}/app_version').status_code == 200:
                break

        # file/folder naming
        self.download_path_template = args['dirname_pattern']
        self.filename_template = args['filename_pattern']
        self.inline_filename_template = args['inline_filename_pattern']
        self.other_filename_template = args['other_filename_pattern']
        self.user_filename_template = args['user_filename_pattern']
        self.date_strf_pattern = args['date_strf_pattern']
        self.yt_dlp_args = args['yt_dlp_args']
        self.restrict_ascii = args['restrict_names']

        self.archive_file = args['archive']
        self.archive_list = []
        self.post_errors = 0

        # controls what to download/save
        self.attachments = not args['skip_attachments']
        self.inline = args['inline']
        self.content = args['content']
        self.extract_links = args['extract_links']
        self.extract_all_links = args['extract_all_links']
        self.comments = args['comments']
        self.json = args['json']
        self.yt_dlp = args['yt_dlp']
        self.k_fav_posts = args['kemono_fav_posts']
        self.c_fav_posts = args['coomer_fav_posts']
        self.k_fav_users = args['kemono_fav_users']
        self.c_fav_users = args['coomer_fav_users']
        self.icon_banner = []
        if args['icon']:
            self.icon_banner.append('icon')
        if args['banner']:
            self.icon_banner.append('banner')
        self.dms = args['dms']
        self.announcements = args['announcements']

        # controls files to ignore
        self.overwrite = args['overwrite']
        self.only_ext = args['only_filetypes']
        self.not_ext = args['skip_filetypes']
        self.max_size = args['max_filesize']
        self.min_size = args['min_filesize']
        self.only_filename = args['only_filename']
        self.not_filename = args['skip_filename']

        # controlls posts to ignore
        self.date = args['date']
        self.datebefore = args['datebefore']
        self.dateafter = args['dateafter']
        self.user_up_datebefore = args['user_updated_datebefore']
        self.user_up_dateafter = args['user_updated_dateafter']
        self.only_postname = args['only_postname']
        self.not_postname = args['skip_postname']

        # other
        self.retry = args['retry']
        self.no_part = args['no_part_files']
        self.ratelimit_sleep = args['ratelimit_sleep']
        self.ratelimit_ms = args['ratelimit_ms']
        self.post_timeout = args['post_timeout']
        self.simulate = args['simulate']
        self.local_hash = args['local_hash']
        self.dupe_check = args['dupe_check']
        self.dupe_check_template = args['dupe_check_pattern']
        self.force_unlisted = args['force_unlisted']
        self.retry_403 = args['retry_403']
        self.fp_added = args['fp_added']
        self.fancards = args['fancards']
        self.cookie_domains = args['cookie_domains']
        self.proxy_agent = args['proxy_agent']
        self.force_dss = args['force_dss']
        self.archives_password = args['archives_password']
        self.auto_extract = True  # 新增自动解压选项
        self.hash_filename = '.extracted_hash'  # 用于存储解压后文件的hash

        self.session = RefererSession(
            proxy_agent = self.proxy_agent,
            max_retries_429 = self.retry,
            sleep_429 = self.ratelimit_sleep
        )
        retries = Retry(
            total=self.retry,
            backoff_factor=0.1,
            status_forcelist=[ 500, 502, 503, 504 ]
        )
        self.session.mount('https://', HTTPAdapter(max_retries=retries))
        self.session.mount('http://', HTTPAdapter(max_retries=retries))

        self.proxies = {'http': args['proxy'], 'https': args['proxy']}
        self.session.proxies = self.proxies

        self.start_download()

    def get_creators(self, domain:str):
        # get site creators
        creators_api = f"https://{domain}/api{self.api_ver}/creators.txt"
        logger.debug(f"Getting creator json from {creators_api}")
        if self.force_unlisted:
            return []
        resp = self.session.get(url=creators_api, cookies=self.cookies, headers=self.headers, timeout=self.timeout)
        # json.loads accepts bytes, I'm not sure if leave it like auto-detect is a good idea or not
        resp_content_decode = resp.content.decode('utf-8')
        return json.loads(resp_content_decode)

    def get_user(self, user_id:str, service:str):
        for creator in self.creators:
            if creator['id'] == user_id and creator['service'] == service:
                return creator
        return None

    def get_favorites(self, domain:str, fav_type:str, retry:int, services:list = None):
        fav_api = f'https://{domain}/api{self.api_ver}/account/favorites?type={fav_type}'
        logger.debug(f"Getting favorite json from {fav_api}")
        response = self.session.get(url=fav_api, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        if response.status_code == 401:
            logger.error(f"Failed to get favorites: {response.status_code} {response.reason} | Bad cookie file")
            return
        if not response.ok:
            if retry>0:
                logger.exception(f"Failed to get favorites: {response.status_code} {response.reason} | Retrying")
                self.get_favorites(domain=domain, fav_type=fav_type, retry=retry-1, services=services)
                return
            logger.error(f"Failed to get favorites: {response.status_code} {response.reason} | All retries failed")
            return
        for favorite in response.json():
            if fav_type == 'post':
                self.get_post(f"https://{domain}/{favorite['service']}/user/{favorite['user']}/post/{favorite['id']}", retry=self.retry)
            if fav_type == 'artist':
                if not (favorite['service'] in services or 'all' in services):
                    logger.info(f"Skipping user {favorite['name']} | Service {favorite['service']} was not requested")
                    continue
                self.get_post(f"https://{domain}/{favorite['service']}/user/{favorite['id']}", retry=self.retry)

    def get_post(self, url:str, retry:int, chunk=0, first=True):
        found = re.search(r'(https://((?:kemono|coomer)\.(?:party|su))/)(([^/]+)/user/([^/]+)($|/post/[^/]+))', url)
        if not found:
            logger.error(f"Unable to find url parameters for {url}")
            return
        api = f"{found.group(1)}api{self.api_ver}/{found.group(3)}"
        site = found.group(2)
        service = found.group(4)
        user_id = found.group(5)
        is_post = found.group(6)
        user = self.get_user(user_id, service)
        if not user:
            if self.force_unlisted:
                user={'favorited': 0, 'id': user_id, 'indexed': 1666666666, 'name': user_id, 'service': service, 'updated': 1666666666}
            else:
                logger.error(f"Unable to find user info in creators list | {service} | {user_id}")
                return
        if not is_post:
            if self.skip_user(user):
                return
        logger.info(f"Downloading posts from {site} | {service} | {user['name']} | {user['id']}")
        while True:
            if is_post:
                logger.debug(f"Requesting post json from: {api}")
                response = self.session.get(url=api, cookies=self.cookies, headers=self.headers, timeout=self.timeout)
                if response.status_code == 429:
                    logger.warning(f"Failed to request post json from: {api} | 429 Too Many Requests | All retries failed")
                    return
            else:
                logger.debug(f"Requesting user json from: {api}?o={chunk}")
                response = self.session.get(url=f"{api}?o={chunk}", cookies=self.cookies, headers=self.headers, timeout=self.timeout)
                if response.status_code == 429:
                    logger.warning(f"Failed to request user json from: {api}?o={chunk} | 429 Too Many Requests | All retries failed")
                    return
            json = response.json()
            if not json:
                if is_post:
                    logger.error(f"Unable to find post json for {api}")
                elif chunk == 0:
                    logger.error(f"Unable to find user json for {api}?o={chunk}")
                return # completed
            if is_post and isinstance(json, dict) and json.get('post'):
                json = json.get('post')
            if not isinstance(json,list):
                json=[json]
            for post in json:
                # only download once
                if not is_post and first:
                    try:
                        post_tmp = self.clean_post(post, user, site)
                        logger.debug(f"Downloading icon and/or banner | {user['name']} | {user['id']}")
                        self.download_icon_banner(post_tmp, self.icon_banner, retry=self.retry)
                        if self.dms:
                            logger.debug(f"Writting dms | {user['name']} | {user['id']}")
                            self.write_dms(post_tmp,retry=self.retry)
                        if self.fancards:
                            logger.debug(f"Downloading fancards | {user['name']} | {user['id']}")
                            self.download_fancards(post_tmp,retry=self.retry)
                        if self.announcements:
                            logger.debug(f"Writting announcements | {user['name']} | {user['id']}")
                            self.write_announcements(post_tmp,retry=self.retry)
                        first = False
                    except:
                        if retry > 0:
                            logger.warning(f"Failed to get icon, banner, dms, fancards or announcements | Retrying")
                            self.get_post(url=url, retry=retry-1, chunk=chunk, first=True)
                        else:
                            logger.error(f"Failed to get icon, banner, dms, fancards or announcements | All retries failed")
                        return
                comments_original=self.comments
                self.comments=False
                post_tmp = self.clean_post(post, user, site)
                if self.skip_post(post_tmp):
                    continue
                self.comments=comments_original
                post = self.clean_post(post, user, site)
                try:
                    self.download_post(post)
                    if self.post_timeout:
                        logger.info(f"Sleeping for {self.post_timeout} seconds.")
                        time.sleep(self.post_timeout)
                except:
                    logger.exception("Unable to download post | service:{service} user_id:{user_id} post_id:{id}".format(**post['post_variables']))
                self.comp_posts.append("https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']))
            chunk_size = 50
            if len(json) < chunk_size:
                return # completed
            chunk += chunk_size


    def download_icon_banner(self, post:dict, img_types:list, retry:int):
        for img_type in img_types:
            if post['post_variables']['service'] in {'dlsite'}:
                logger.warning(f"Profile {img_type}s are not supported for {post['post_variables']['service']} users")
                continue
            if post['post_variables']['service'] in {'gumroad'} and img_type == 'banner':
                logger.warning(f"Profile {img_type}s are not supported for {post['post_variables']['service']} users")
                continue
            image_url = "https://{site}/{img_type}s/{service}/{user_id}".format(img_type=img_type, **post['post_variables'])
            response = self.session.get(url=image_url,headers=self.headers, cookies=self.cookies, timeout=self.timeout)
            if response.status_code == 429:
                logger.error(f"Unable to download profile {img_type} for {post['post_variables']['username']} | 429 Too Many Requests | All retries failed")
                return
            try:
                image = Image.open(BytesIO(response.content))
                file_variables = {
                    'filename':img_type,
                    'ext':image.format.lower()
                }
                file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
                if os.path.exists(file_path):
                    logger.info(f"Skipping: {os.path.split(file_path)[1]} | File already exists")
                    continue
                logger.info(f"Downloading: {os.path.split(file_path)[1]}")
                logger.debug(f"Downloading to: {file_path}")
                if not self.simulate:
                    if not os.path.exists(os.path.split(file_path)[0]):
                        os.makedirs(os.path.split(file_path)[0])
                    image.save(file_path, format=image.format)
            except:
                logger.error(f"Unable to download profile {img_type} for {post['post_variables']['username']}")

    def write_dms(self, post:dict, retry:int):
        if post['post_variables']['service'] != 'patreon':
            logger.debug("Skipping dms for non patreon user https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        post_url = "https://{site}/api{api_ver}/{service}/user/{user_id}/dms".format(**post['post_variables'],api_ver=self.api_ver)
        response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        if not response.ok:
            if response.status_code==429:
                logger.warning("Unable to download DMs for {service} {user_id} | 429 | All retries failed".format(**post['post_variables']))
                return
            else:
                logger.warning("Unable to download DMs for {service} {user_id} | {code} | Retrying.".format(core=response.status_code,**post['post_variables']))
            if retry > 0:
                self.write_dms(post=post,retry=retry-1)
            else:
                logger.error("Unable to download DMs for {service} {user_id} | {code} | All retries failed.".format(core=response.status_code,**post['post_variables']))
            return
        page_json = response.json()
        if page_json.get('props') is None or page_json.get('props').get('dm_count') < 1:
            logger.info("No DMs found for https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        file_variables = {
            'filename':'{dmc} direct messages'.format(dmc=page_json.get('props').get('dm_count')),
            'ext':'json'
        }
        dms_json = page_json.get('props').get('dms')
        if isinstance(dms_json,list):
            dms_json = dict(enumerate(dms_json))
        file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
        self.write_to_file(file_path, dms_json)

    def download_fancards(self, post:dict, retry:int):
        if post['post_variables']['service'] != 'fanbox':
            logger.debug("Skipping fancards for non fanbox user https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        post_url = "https://{site}/api{api_ver}/{service}/user/{user_id}/fancards".format(**post['post_variables'],api_ver=self.api_ver)
        logger.info(f"Downloading fancards {post_url}")
        response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        if not response.ok:
            if response.status_code==429:
                logger.warning("Unable to find Fancards for {service} {user_id} | 429 | All retries failed".format(**post['post_variables']))
                return
            else:
                logger.warning("Unable to find Fancards for {service} {user_id} | {code} | Retrying.".format(core=response.status_code,**post['post_variables']))
            if retry > 0:
                self.download_fancards(post=post,retry=retry-1)
            else:
                logger.error("Unable to find Fancards for {service} {user_id} | {code} | All retries failed.".format(core=response.status_code,**post['post_variables']))
            return
        page_json = response.json()
        fancards_json = page_json if isinstance(page_json, list) else [page_json]
        if not len(fancards_json):
            logger.info("No fancards found for https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        for fancard in fancards_json:
            fancard_added = datetime.datetime.fromisoformat(fancard.get('added'))
            fancard_title = datetime.datetime.strftime(fancard_added,'Added %Y-%m')
            fancard_url = fancard.get('server') + fancard.get('path')
            fancard_filename = fancard.get('hash')
            fancard_ext = fancard.get('ext').strip('.')
            file_variables = {
                'filename':'{title}_{name}'.format(title=fancard_title,name=fancard_filename),
                'ext':fancard_ext,
                'url':fancard_url,
                'hash':fancard_filename,
                'referer':post_url
            }
            file_path = compile_file_path(os.path.join(post['post_path'],'Fancards'), post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
            self.download_file({"file_path":file_path,"file_variables":file_variables}, retry=self.retry, post=post) #dummy postid

    def write_announcements(self, post:dict, retry:int):
        post_url = "https://{site}/api{api_ver}/{service}/user/{user_id}/announcements".format(**post['post_variables'],api_ver=self.api_ver)
        response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        if not response.ok:
            if response.status_code==429:
                logger.warning("Unable to get announcements for {service} {user_id} | 429 | All retries failed".format(**post['post_variables']))
                return
            else:
                logger.warning("Unable to get announcements for {service} {user_id} | {code} | Retrying.".format(core=response.status_code,**post['post_variables']))
            if retry > 0:
                self.write_announcements(post=post,retry=retry-1)
            else:
                logger.error("Unable to get announcements for {service} {user_id} | {code} | All retries failed.".format(core=response.status_code,**post['post_variables']))
            return
        if not len(response.json()):
            logger.info("No announcements found for https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return

        announcements = ""
        for announcement in response.json():
            ann_pub_date = f'published: {announcement.get("published")}'
            ann_add_date = f'added: {announcement.get("added")}'
            announcements += f'# {ann_pub_date} | {ann_add_date}\n\n'
            announcements += f'{announcement["content"].strip()}\n\n'

        file_variables = {
            'filename':'announcements',
            'ext':'txt'
        }
        file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
        overwrite_original = self.overwrite
        if os.path.exists(file_path) and os.path.getsize(file_path) < len(announcements):
            self.overwrite = True
        self.write_to_file(file_path, announcements)
        self.overwrite = overwrite_original

    def get_inline_images(self, post, content_soup):
        # only get images that are hosted by the .party site
        inline_images = [inline_image for inline_image in content_soup.find_all("img") 
                            if inline_image.get('src') and inline_image.get('src')[0] == '/']
        for index, inline_image in enumerate(inline_images):
            file = {}
            filename, file_extension = os.path.splitext(inline_image['src'].rsplit('/')[-1])
            m = re.search(r'[a-zA-Z0-9]{64}', inline_image['src'])
            file_hash = m.group(0) if m else None
            file['file_variables'] = {
                'filename': filename,
                'ext': file_extension[1:],
                'url': f"https://{post['post_variables']['site']}/data{inline_image['src']}",
                'hash': file_hash,
                'index': f"{index + 1}".zfill(len(str(len(inline_images)))),
                'referer': f"https://{post['post_variables']['site']}/{post['post_variables']['service']}/user/{post['post_variables']['user_id']}/post/{post['post_variables']['id']}"
            }
            file['file_path'] = compile_file_path(post['post_path'], post['post_variables'], file['file_variables'], self.inline_filename_template, self.restrict_ascii)
            html_loc = pathlib.Path(compile_file_path(post['post_path'], post['post_variables'], {'filename':'dummy','ext':'html'}, self.other_filename_template, self.restrict_ascii)).parent
            # set local image location in html
            inline_image['src'] = os.path.relpath(file['file_path'],html_loc)
            post['inline_images'].append(file)
        return content_soup

    def compile_content_links(self, post, content_soup, embed_links):
        href_links = content_soup.find_all(href=True)
        post['links']['text'] = embed_links
        for href_link in href_links:
            post['links']['text'] += f"{href_link['href']}\n"
        post['links']['file_variables'] = {
            'filename':'links',
            'ext':'txt'
        }
        post['links']['file_path'] = compile_file_path(post['post_path'], post['post_variables'], post['links']['file_variables'], self.other_filename_template, self.restrict_ascii)

    def get_comments(self, post:dict):
        try:
            post_url = "https://{site}/api{api_ver}/{service}/user/{user_id}/post/{id}/comments".format(**post['post_variables'],api_ver=self.api_ver)
            response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
            if response.status_code == 429:
                logger.warning(f"Failed to get post comments | 429 Too Many Requests | All retries failed")
            page_json = response.json()
            no_comments = isinstance(page_json, dict) and page_json.get('error')
            if no_comments:
                logger.debug(page_json.get('error'))
                return ''
            comments_json = page_json if isinstance(page_json, list) else []
            file_variables = {
                'filename':'{dmc} comments'.format(dmc=len(comments_json)),
                'ext':'json'
            }
            if isinstance(comments_json,list):
                comments_json = dict(enumerate(comments_json))
            file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.other_filename_template, self.restrict_ascii)
            self.write_to_file(file_path, comments_json)
            return True
        except:
            self.post_errors += 1
            logger.exception("Failed to get post comments")

    def compile_post_content(self, post, content_soup, comment_soup, embed):
        post['content']['text'] = f"{content_soup}\n{embed}\n{comment_soup}"
        post['content']['file_variables'] = {
            'filename':'content',
            'ext':'html'
        }
        post['content']['file_path'] = compile_file_path(post['post_path'], post['post_variables'], post['content']['file_variables'], self.other_filename_template, self.restrict_ascii)

    def clean_post(self, post:dict, user:dict, domain:str):
        new_post = {}
        # set post variables
        new_post['post_variables'] = {}
        new_post['post_variables']['title'] = post['title']
        new_post['post_variables']['id'] = post['id']
        new_post['post_variables']['user_id'] = post['user']
        new_post['post_variables']['username'] = user['name']
        new_post['post_variables']['site'] = domain
        new_post['post_variables']['service'] = post['service']
        new_post['post_variables']['added'] = self.format_time_by_type(post['added']) if post['added'] else None
        new_post['post_variables']['updated'] = self.format_time_by_type(post['edited']) if post['edited'] else None
        new_post['post_variables']['user_updated'] = self.format_time_by_type(user['updated']) if user['updated'] else None
        new_post['post_variables']['published'] = self.format_time_by_type(post['published']) if post['published'] else None
        new_post['post_variables']['tags'] = post['tags']
        new_post['post_variables']['poll'] = post['poll']

        new_post['post_path'] = compile_post_path(new_post['post_variables'], self.download_path_template, self.restrict_ascii)

        new_post['attachments'] = []
        if self.attachments:
            # add post file to front of attachments list if it doesn't already exist
            if post['file'] and not post['file'] in post['attachments']:
                post['attachments'].insert(0, post['file'])
            # loop over attachments and set file variables
            for index, attachment in enumerate(post['attachments']):
                file = {}
                if attachment.get('name') and isinstance(attachment.get('name'),str):
                    filename, file_extension = os.path.splitext(attachment['name'])
                elif attachment.get('path') and isinstance(attachment.get('path'),str):
                    filename, file_extension = os.path.splitext(attachment['path'].split('/')[-1])
                else:
                    continue
                m = re.search(r'[a-zA-Z0-9]{64}', attachment['path'])
                file_hash = m.group(0) if m else None
                file['file_variables'] = {
                    'filename': filename,
                    'ext': file_extension[1:],
                    'url': f"https://{domain}/data{attachment['path']}",
                    'hash': file_hash,
                    'index': f"{index + 1}".zfill(len(str(len(post['attachments'])))),
                    'referer': f"https://{domain}/{post['service']}/user/{post['user']}/post/{post['id']}"
                }
                file['file_path'] = compile_file_path(new_post['post_path'], new_post['post_variables'], file['file_variables'], self.filename_template, self.restrict_ascii)
                new_post['attachments'].append(file)

        new_post['inline_images'] = []
        content_soup = BeautifulSoup(post['content'], 'html.parser')
        if self.inline:
            content_soup = self.get_inline_images(new_post, content_soup)

        comment_soup = ''

        new_post['content'] = {'text':None,'file_variables':None, 'file_path':None}
        embed = "{subject}\n{url}\n{description}".format(**post['embed']) if post['embed'] else ''
        if (self.content or self.comments) and (content_soup or comment_soup or embed):
            self.compile_post_content(new_post, content_soup.prettify(), comment_soup, embed)

        new_post['links'] = {'text':None,'file_variables':None, 'file_path':None}
        embed_url = "{url}\n".format(**post['embed']) if post['embed'] else ''
        if self.extract_links or self.extract_all_links:
            self.compile_content_links(new_post, content_soup, embed_url)

        return new_post

    def download_post(self, post:dict):
        # might look buggy if title has new lines in it
        logger.info("Downloading Post | {title}".format(**post['post_variables']))
        logger.debug("Post URL: https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']))
        self.download_attachments(post)
        self.download_inline(post)
        self.write_content(post)
        if self.comments:
            self.get_comments(post)
        self.write_links(post)
        if self.json:
            self.write_json(post)
        self.download_yt_dlp(post)
        self.write_archive(post)
        self.post_errors = 0

    def download_attachments(self, post:dict):
        # download the post attachments
        for file in post['attachments']:
            try:
                self.download_file(file, retry=self.retry, post=post)
            except:
                self.post_errors += 1
                logger.exception(f"Failed to download: {file['file_path']}")

    def download_inline(self, post:dict):
        # download the post inline files
        for file in post['inline_images']:
            try:
                self.download_file(file, retry=self.retry, post=post)
            except:
                self.post_errors += 1
                logger.exception(f"Failed to download: {file['file_path']}")

    def write_content(self, post:dict):
        # write post content
        if post['content']['text']:
            try:
                self.write_to_file(post['content']['file_path'], post['content']['text'])
            except:
                self.post_errors += 1
                logger.exception(f"Failed to save content")

    def write_links(self, post:dict):
        # Write post content links
        if post['links']['text']:
            try:
                if self.extract_all_links:
                    self.write_links_to_file(f"./{post['post_variables']['username']}.txt", post['links']['text'])
                if self.extract_links:
                    self.write_to_file(post['links']['file_path'], post['links']['text'])
            except:
                self.post_errors += 1
                logger.exception(f"Failed to save content links")


    def write_json(self, post:dict):
        try:
            # add this to clean post function
            file_variables = {
                'filename':'json',
                'ext':'json'
            }
            file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.other_filename_template, self.restrict_ascii)
            self.write_to_file(file_path, post)
        except:
            self.post_errors += 1
            logger.exception(f"Failed to save json")

    def write_to_file(self, file_path, file_content):
        # check if file exists and if should overwrite
        if os.path.exists(file_path) and not self.overwrite:
            logger.info(f"Skipping: {os.path.split(file_path)[1]} | File already exists")
            return
        logger.info(f"Writing: {os.path.split(file_path)[1]}")
        logger.debug(f"Writing to: {file_path}")
        if not self.simulate:
            # create folder path if it doesn't exist
            if not os.path.exists(os.path.split(file_path)[0]):
                os.makedirs(os.path.split(file_path)[0])
            # write to file
            if isinstance(file_content, dict):
                with open(file_path,'w') as f:
                    json.dump(file_content, f, indent=4, sort_keys=True)
            else:
                with open(file_path,'wb') as f:
                    f.write(file_content.encode("utf-8"))

    def write_links_to_file(self, file_path, file_content):
        with open(file_path,'a') as f:
            print(file_content, file=f)

    def download_file(self, file:dict, retry:int, post:dict):
        # download a file
        if self.skip_file(file,post=post):
            return

        part_file = f"{file['file_path']}.part" if not self.no_part else file['file_path']

        logger.info(f"Downloading: {os.path.split(file['file_path'])[1]}")
        logger.debug(f"Downloading from: {file['file_variables']['url']}")
        logger.debug(f"Downloading to: {part_file}")

        request_headers={'Referer':file['file_variables']['referer']}

        # archives password
        if self.archives_password and file['file_variables']['ext'] in ('zip','7z','rar'):
            try:
                passwd_api = "https://{site}/api{api_ver}/posts/archives/{hash}".format(**post['post_variables'],**file['file_variables'],api_ver=self.api_ver)
                passwd_resp = self.session.get(url=passwd_api, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
                passwd_json = passwd_resp.json()
            except:
                passwd_json = None
            if passwd_json:
                if passwd_json.get('archive') and passwd_json.get('archive').get('password'):
                    passwd_filevar = dict(file['file_variables'])
                    passwd_filevar.update({'ext':'pw'})
                    passwd_filepath = compile_file_path(post['post_path'], post['post_variables'], passwd_filevar, self.filename_template, self.restrict_ascii)
                    self.write_to_file(passwd_filepath, passwd_json.get('archive').get('password'))

        if self.force_dss:
            dss_letter=isinstance(self.force_dss,str) and self.force_dss[0]
            url_pre_redir=file['file_variables']['url']
            url_redir=None
            if url_pre_redir.startswith('https://kemono') or url_pre_redir.startswith('https://coomer'):
                resp=self.session.get(url=url_pre_redir, stream=False, headers=dict(**self.headers,**request_headers), cookies=self.cookies, timeout=self.timeout, allow_redirects=False)
                if resp.status_code == 302:
                    url_redir = resp.headers['Location']
                    url_match = re.match('(https://[a-z])[0-9]\\.',url_redir)
                    if url_match:
                        url_redir=url_redir.replace(url_match.group(1),'https://'+dss_letter)
                    file['file_variables']['url'] = url_redir

        # try to resume part file
        resume_size = 0
        if os.path.exists(part_file) and not self.overwrite and os.path.getsize(part_file):
            resume_size = os.path.getsize(part_file)
            logger.info(f"Trying to resuming partial download | Resume size: {resume_size} bytes")
            request_headers['Range']=f"bytes={resume_size}-"

        try:
            if self.headcheck:
                head_ref = self.session.get(url=file['file_variables']['url'], stream=False, headers=dict(**self.headers,**{'Range':f'bytes={resume_size}-{resume_size+1023}'}), cookies=self.cookies, timeout=self.timeout).content
            response = self.session.get(url=file['file_variables']['url'], stream=True, headers=dict(**self.headers,**request_headers), cookies=self.cookies, timeout=self.timeout)
        except:
            logger.exception(f"Failed to get responce: {file['file_variables']['url']} | Retrying")
            if retry > 0:
                self.download_file(file, retry=retry-1, post=post)
                return
            logger.error(f"Failed to get responce: {file['file_variables']['url']} | All retries failed")
            self.post_errors += 1
            return

        # responce status code checking
        if response.status_code == 404:
            logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | 404 Not Found")
            self.post_errors += 1
            return

        if response.status_code == 403:
            for _ in range(self.retry_403):
                logger.info('A 403 encountered, retry without session.')
                try:
                    response = requests.get(url=file['file_variables']['url'], stream=True, headers=request_headers, timeout=self.timeout,proxies=self.proxies)
                except:
                    logger.exception(f"Failed to get responce: {file['file_variables']['url']} | Retrying")
                    if retry > 0:
                        self.download_file(file, retry=retry-1, post=post)
                        return
                    logger.error(f"Failed to get responce: {file['file_variables']['url']} | All retries failed")
                    self.post_errors += 1
                    return
                if response.status_code != 403:
                    break
            if response.status_code == 403:
                logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | 403 Forbidden")
                self.post_errors += 1
                return

        if response.status_code == 416:
            logger.warning(f"Failed to download: {os.path.split(file['file_path'])[1]} | 416 Range Not Satisfiable | Assuming broken server hash value")
            content_length = self.session.get(url=file['file_variables']['url'], stream=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout).headers.get('content-length', '')
            if int(content_length) == resume_size:
                logger.debug("Correct amount of bytes downloaded | Assuming download completed successfully")
                if self.overwrite:
                    os.replace(part_file, file['file_path'])
                else:
                    os.rename(part_file, file['file_path'])
                return
            logger.error("Incorrect amount of bytes downloaded | Something went so wrong I have no idea what happened | Saving file with suffix in name")
            # os.remove(part_file)
            filepath=os.path.splitext(file['file_path'])
            filepath=filepath[0]+'_statuscode416'+filepath[1]
            if self.overwrite:
                os.replace(part_file, filepath)
            else:
                os.rename(part_file, filepath)
            self.post_errors += 1
            return

        if response.status_code == 429:
            # already retried for 429
            logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | 429 Too Many Requests | All retries failed")
            self.post_errors += 1
            return
        if not response.ok:
            logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | {response.status_code} {response.reason}")
            self.post_errors += 1
            return

        total = int(response.headers.get('content-length', 0))
        if total:
            total += resume_size

        if not self.simulate:
            try:
                if not os.path.exists(os.path.split(file['file_path'])[0]):
                    os.makedirs(os.path.split(file['file_path'])[0])
                first_chunk=True
                with open(part_file, 'wb' if resume_size == 0 else 'ab') as f:
                    start = time.time()
                    downloaded = resume_size
                    print_download_bar(total, downloaded, resume_size, start)
                    iter_chunk_size = 256<<10
                    puff = bytes()
                    for chunk in response.iter_content(chunk_size=iter_chunk_size):
                        if first_chunk:
                            first_chunk=False
                            if self.headcheck:
                                if chunk[:len(head_ref)]!=head_ref:
                                    raise Exception("Head Check Mismatch")
                        puff += chunk
                        downloaded += len(chunk)
                        if len(puff) >= (32<<20)//iter_chunk_size*iter_chunk_size:
                            f.write(puff)
                            puff = bytes()
                        print_download_bar(total, downloaded, resume_size, start)
                    if puff:
                        f.write(puff)
                        puff = bytes()
                print()
            except Exception as exc:
                # assuming puffered content is good
                with open(part_file, 'ab') as f:
                    f.write(puff)
                    puff = bytes()
                if retry > 0:
                    logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | Exception: {exc} | Retrying")
                    self.download_file(file, retry=retry-1, post=post)
                    return
                logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | Exception: {exc} | All retries failed")
                self.post_errors += 1
                return

            # verify download
            local_hash = get_file_hash(part_file)
            logger.debug(f"Local File hash: {local_hash}")
            logger.debug(f"Sever File hash: {file['file_variables']['hash']}")
            if local_hash != file['file_variables']['hash']:
                if file['file_variables']['hash'] !=None:
                    logger.warning(f"File hash did not match server! | Retrying")
                    if os.path.getsize(part_file)==total:
                        os.remove(part_file)
                    if retry > 0:
                        self.download_file(file, retry=retry-1, post=post)
                        return
                    logger.error(f"File hash did not match server! | All retries failed")
                    self.post_errors += 1
                    return
                else:
                    logger.warning(f"No hash from server! | Saving file with suffix in name")
                    filepath=os.path.splitext(file['file_path'])
                    filepath=filepath[0]+'_noserverhash'+filepath[1]
                    if self.overwrite:
                        os.replace(part_file, filepath)
                    else:
                        os.rename(part_file, filepath)
                    return
            # remove .part from file name
            if self.overwrite:
                os.replace(part_file, file['file_path'])
            else:
                os.rename(part_file, file['file_path'])

            # 在成功下载后添加解压逻辑
            if self.auto_extract and file['file_variables']['ext'].lower() in ['zip', '7z', 'rar']:
                self.extract_archive(file['file_path'], file['file_variables']['hash'], is_new_download=True)

    def download_yt_dlp(self, post:dict):
        # download from video streaming site
        # if self.yt_dlp and post['embed']:
            pass
            # my_yt_dlp(post['embed']['url'], post['post_path'], self.yt_dlp_args)

    def load_archive(self):
        # load archived posts
        if self.archive_file and os.path.exists(self.archive_file):
            with open(self.archive_file,'r') as f:
                self.archive_list = f.read().splitlines()

    def write_archive(self, post:dict):
        if self.archive_file and self.post_errors == 0 and not self.simulate:
            with open(self.archive_file,'a') as f:
                f.write("https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']) + '\n')

    def skip_user(self, user:dict):
        # check last update date
        if self.user_up_datebefore or self.user_up_dateafter:
            if check_date(self.get_date_by_type(user['updated']), None, self.user_up_datebefore, self.user_up_dateafter):
                logger.info(f"Skipping user {user['id']} | user updated date not in range")
                return True
        return False

    def skip_post(self, post:dict):
        # check if the post should be downloaded
        if self.archive_file:
            post_url = "https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables'])
            post_url_another = post_url.replace('.su','.party') if post['post_variables']['site'].endswith('.su') else post_url.replace('.party','.su')
            if post_url in self.archive_list or post_url_another in self.archive_list:
                logger.info(f"Skipping post {post['post_variables']['id']} | post already archived") # add some numbers to indicate that the script isn't frozen when a lot of posts skipped and your screen is full of this message
                return True

        if self.date or self.datebefore or self.dateafter:
            if not post['post_variables']['published']:
                logger.info(f"Skipping post {post['post_variables']['id']} | post published date not in range")
                return True
            elif check_date(self.get_date_by_type(post['post_variables']['published' if not self.fp_added else 'added'], self.date_strf_pattern), self.date, self.datebefore, self.dateafter):
                logger.info(f"Skipping post {post['post_variables']['id']} | post published date not in range")
                return True

        if "https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']) in self.comp_posts:
            logger.info(f"Skipping post {post['post_variables']['id']} | post was already downloaded this session")
            return True

        # check post title
        if self.only_postname:
            skip = True
            for w in self.only_postname:
                if w.lower() in post['post_variables']['title'].lower():
                    skip = False
                    break
            if skip:
                logger.info(f"Skipping post {post['post_variables']['id']} | post title does not contain any of the given word(s): {self.only_postname}")
                return True
                
        if self.not_postname:
            for w in self.not_postname:
                if w.lower() in post['post_variables']['title'].lower():
                    logger.info(f"Skipping post {post['post_variables']['id']} | post title contains word: {w}")
                    return True
        
        return False

    def skip_file(self, file:dict, post:dict):
        # 检查是否是已解压的文件
        if file['file_variables']['ext'].lower() in ['zip', '7z', 'rar']:
            extract_dir = os.path.dirname(file['file_path'])
            hash_file = os.path.join(extract_dir, self.hash_filename)
            if os.path.exists(hash_file):
                try:
                    with open(hash_file, 'r') as f:
                        hash_data = json.load(f)
                        if file['file_variables']['hash'] in hash_data:
                            logger.info(f"跳过下载: {os.path.split(file['file_path'])[1]} | 文件已存在hash记录")
                            return True
                except:
                    pass

        # 检查文件是否存在
        if not self.overwrite:
            if os.path.exists(file['file_path']):
                confirm_msg = ''
                if 'hash' in file['file_variables'] and file['file_variables']['hash'] != None and self.local_hash:
                    local_hash = get_file_hash(file['file_path'])
                    if local_hash != file['file_variables']['hash']:
                        logger.warning(f"Corrupted file detected, remove this file and try to redownload | path: {file['file_path']} " + 
                                    f"local hash: {local_hash} server hash: {file['file_variables']['hash']}")
                        os.remove(file['file_path'])
                        return False
                    confirm_msg = ' | Hash confirmed'
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File already exists{confirm_msg}")
                return True

        # check file name extention
        if self.only_ext:
            if not file['file_variables']['ext'].lower() in self.only_ext:
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File extention {file['file_variables']['ext']} not found in include list {self.only_ext}")
                return True
        if self.not_ext:
            if file['file_variables']['ext'].lower() in self.not_ext:
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File extention {file['file_variables']['ext']} found in exclude list {self.not_ext}")
                return True

        # check file name 
        if self.only_filename:
            skip = True
            for w in self.only_filename:
                if w.lower() in file['file_variables']['filename'].lower():
                    skip = False
            if skip:
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File name does not contain any of the given word(s): {self.only_filename} ")
                return True
                
        if self.not_filename:
            for w in self.not_filename:
                if w.lower() in file['file_variables']['filename'].lower():
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File name contains word: {w}")
                    return True

        # check file size
        if self.min_size or self.max_size:
            file_size = requests.get(file['file_variables']['url'], cookies=self.cookies, stream=True,proxies=self.proxies).headers.get('content-length', 0)
            if int(file_size) == 0:
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size not included in file header")
                    return True
            if self.min_size and self.max_size:
                if not (self.min_size <= int(file_size) <= self.max_size):
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size in bytes {file_size} was not between {self.min_size} and {self.max_size}")
                    return True
            elif self.min_size:
                if not (self.min_size <= int(file_size)):
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size in bytes {file_size} was not >= {self.min_size}")
                    return True
            elif self.max_size:
                if not (int(file_size) <= self.max_size):
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size in bytes {file_size} was not <= {self.max_size}")
                    return True
        return False

    def extract_archive(self, archive_path, hash_value, is_new_download=False):
        """解压缩文件并保存hash信息"""
        try:
            base_dir = os.path.dirname(archive_path)
            file_name = os.path.splitext(os.path.basename(archive_path))[0].strip()  # 移除文件名的首尾空格
            extract_dir = os.path.join(base_dir, file_name)
            file_ext = os.path.splitext(archive_path)[1].lower()
            
            # 检查是否有解压失败标记（仅对新下载的文件检查）
            fail_mark = os.path.join(base_dir, f"{file_name}.extract_failed")
            if is_new_download and os.path.exists(fail_mark):
                logger.info(f"跳过: {os.path.basename(archive_path)} | 之前多次解压失败已标记")
                return False  # 不删除压缩文件，保留它
            
            # 创建解压目标目录
            if not os.path.exists(extract_dir):
                os.makedirs(extract_dir)

            # 尝试解压
            try:
                if file_ext == '.zip':
                    with zipfile.ZipFile(archive_path, 'r') as zip_ref:
                        # 处理文件名中的空格问题
                        for zip_info in zip_ref.filelist:
                            # 修正文件名，移除结尾空格
                            filename = zip_info.filename
                            if filename.endswith(' /') or filename.endswith(' \\'):
                                filename = filename.rstrip(' /\\') + '/'
                            elif filename.endswith(' '):
                                filename = filename.rstrip()
                            
                            # 创建所需的目录
                            target_path = os.path.join(extract_dir, filename)
                            dirname = os.path.dirname(target_path)
                            if not os.path.exists(dirname):
                                os.makedirs(dirname)
                            
                            # 如果不是目录，则解压文件
                            if not filename.endswith('/'):
                                with zip_ref.open(zip_info) as source, open(target_path, 'wb') as target:
                                    shutil.copyfileobj(source, target)
                elif file_ext == '.7z':
                    with py7zr.SevenZipFile(archive_path, 'r') as sz_ref:
                        sz_ref.extractall(extract_dir)
                elif file_ext in ['.rar']:
                    with rarfile.RarFile(archive_path, 'r') as rar_ref:
                        rar_ref.extractall(extract_dir)
                else:
                    logger.warning(f"不支持的压缩格式: {file_ext}")
                    return False

            except (RuntimeError, rarfile.BadRarFile) as e:
                if "encrypted" in str(e).lower() or "password" in str(e).lower():
                    logger.info(f"跳过加密的压缩文件: {os.path.basename(archive_path)}")
                    if os.path.exists(extract_dir) and not os.listdir(extract_dir):
                        try:
                            os.rmdir(extract_dir)
                        except:
                            pass
                    return False
                raise e

            # 保存hash信息（用于防止重复下载）
            hash_file = os.path.join(base_dir, self.hash_filename)
            try:
                with open(hash_file, 'r') as f:
                    hash_data = json.load(f)
            except (FileNotFoundError, json.JSONDecodeError):
                hash_data = {}
            
            hash_data[hash_value] = file_name
            with open(hash_file, 'w') as f:
                json.dump(hash_data, f, indent=2)

            # 删除原压缩文件
            os.remove(archive_path)
            logger.info(f"成功解压到 {file_name} 并删除: {os.path.basename(archive_path)}")
            return True

        except Exception as e:
            logger.error(f"解压失败 {os.path.basename(archive_path)}: {str(e)}")
            
            if not is_new_download:
                # 本地文件解压失败，直接删除
                if os.path.exists(archive_path):
                    os.remove(archive_path)
                logger.info(f"本地压缩文件解压失败，已删除: {os.path.basename(archive_path)}")
            else:
                # 新下载的文件才进行重试计数
                retry_file = os.path.join(base_dir, f"{file_name}.retry_count")
                retry_count = 0
                if os.path.exists(retry_file):
                    with open(retry_file, 'r') as f:
                        retry_count = int(f.read().strip())
                
                retry_count += 1
                if retry_count >= 3:  # 超过3次失败
                    with open(fail_mark, 'w') as f:
                        f.write(f"Extract failed 3 times, last attempt at {datetime.datetime.now()}: {str(e)}")
                    if os.path.exists(retry_file):
                        os.remove(retry_file)
                    logger.error(f"文件 {os.path.basename(archive_path)} 已尝试3次解压均失败，已标记为永久跳过")
                else:
                    with open(retry_file, 'w') as f:
                        f.write(str(retry_count))
                    logger.warning(f"文件 {os.path.basename(archive_path)} 解压失败第{retry_count}次，将重试下载")
                    if "encrypted" not in str(e).lower() and "password" not in str(e).lower():
                        if os.path.exists(archive_path):
                            os.remove(archive_path)
            
            # 删除创建的空目录
            if os.path.exists(extract_dir):
                try:
                    if not os.listdir(extract_dir):
                        os.rmdir(extract_dir)
                except:
                    pass
            return False

    def process_existing_archives(self, directory):
        """处理目录中已存在的压缩文件"""
        for root, _, files in os.walk(directory):
            for file in files:
                if file.lower().endswith(('.zip', '.7z', '.rar')):
                    archive_path = os.path.join(root, file)
                    hash_value = get_file_hash(archive_path)
                    self.extract_archive(archive_path, hash_value, is_new_download=False)

    def start_download(self):
        # 处理已存在的压缩文件
        if self.auto_extract:
            logger.info("处理已存在的压缩文件...")
            self.process_existing_archives(os.getcwd())
            
        self.load_archive()

        urls = []
        domains = []

        for url in self.input_urls:
            domain = parse_url(url)
            if not domain:
                logger.warning(f"URL is not downloadable | {url}")
                continue
            if domain not in self.cookie_domains.values() and self.cookies is not None:
                logger.warning(f"Domain not in cookie files, cookie won't work properly | {url}")
            urls.append(url)
            if not domain in domains: domains.append(domain)

        if self.k_fav_posts or self.k_fav_users:
            if self.cookie_domains['kemono'] not in domains:
                domains.append(self.cookie_domains['kemono'])
        if self.c_fav_posts or self.c_fav_users:
            if self.cookie_domains['coomer'] not in domains:
                domains.append(self.cookie_domains['coomer'])

        for domain in domains:
            try:
                self.creators += self.get_creators(domain)
            except:
                logger.exception(f"Unable to get list of creators from {domain}")
        if not self.creators and not self.force_unlisted:
            logger.error("No creator information was retrieved. | exiting")
            exit()

        if self.k_fav_posts:
            try:
                self.get_favorites(self.cookie_domains['kemono'], 'post', retry=self.retry)
            except:
                logger.exception(f"Unable to get favorite posts from {self.cookie_domains['kemono']}")
        if self.c_fav_posts:
            try:
                self.get_favorites(self.cookie_domains['coomer'], 'post', retry=self.retry)
            except:
                logger.exception(f"Unable to get favorite posts from {self.cookie_domains['coomer']}")
        if self.k_fav_users:
            try:
                self.get_favorites(self.cookie_domains['kemono'], 'artist', retry=self.retry, services=self.k_fav_users)
            except:
                logger.exception(f"Unable to get favorite users from {self.cookie_domains['kemono']}")
        if self.c_fav_users:
            try:
                self.get_favorites(self.cookie_domains['coomer'], 'artist', retry=self.retry, services=self.c_fav_users)
            except:
                logger.exception(f"Unable to get favorite users from {self.cookie_domains['coomer']}")

        for url in urls:
            try:
                self.get_post(url, retry=self.retry)
            except:
                logger.exception(f"Unable to get posts for {url}")

    def get_date_by_type(self, time, date_format = None):
        if isinstance(time, Number):
            t = datetime.datetime.fromtimestamp(time)
        elif isinstance(time, str):
            if date_format is None:
                try:
                    t = datetime.datetime.fromisoformat(time)
                except ValueError:
                    t = datetime.datetime.strptime(time, r'%Y%m%d')
            else:
                t = datetime.datetime.strptime(time, date_format)
        elif time == None:
            return None
        else:
            raise Exception(f'Can not format time {time}')
        return t
                
    def format_time_by_type(self, time):
        t = self.get_date_by_type(time)
        return t.strftime(self.date_strf_pattern) if t != None else t

def main():
    downloader(get_args())
