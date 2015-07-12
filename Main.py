#! /usr/bin/env python3
# -*- coding: utf-8 -*-

import configparser
import subprocess
import threading
import datetime
import zipfile
import socket
import math
import json
import time
import sys
import re
import os
import gi
import urllib.parse
import urllib.request
import http.cookiejar
import concurrent.futures
from decimal import Decimal
from collections import OrderedDict
from urllib.error import URLError, HTTPError

gi.require_version('Gst', '1.0')
gi.require_version('Gtk', '3.0')

from gi.repository import Gst
from gi.repository import Gdk
from gi.repository import Gtk
from gi.repository import GLib
from gi.repository import Pango
from gi.repository import GObject

# Разместить здесь, что-бы не вызвать ошибку инициализации у GstPbutils
Gst.init(None)

from gi.repository import GdkPixbuf
from gi.repository import GstPbutils

try:
    from gi.repository import AppIndicator3
    APP_INDICATOR = True
except:
    APP_INDICATOR = False

# Версия скрипта
SCRIPT_VERSION = '0.0.0.71'

####################################################################
####################################################################

# Обнаружение PROXISERVER
IF_PROXI = urllib.request.ProxyHandler(urllib.request.getproxies())
AUTHHANDLER = urllib.request.HTTPBasicAuthHandler()
MY_COOKIE = urllib.request.HTTPCookieProcessor(
http.cookiejar.CookieJar(
http.cookiejar.DefaultCookiePolicy(
rfc2965=True,
strict_ns_domain=http.cookiejar.DefaultCookiePolicy.DomainStrict,
blocked_domains=["ads.net", ".ads.net"])))
####################################################################
####################################################################

class RadioWin(Gtk.Window):

    def __init__(self):
        super(RadioWin, self).__init__()

        # Путь запуска программы
        self.prog_full_path = os.path.dirname(os.path.realpath(__file__))

        #@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
        # Настройки окна программы по умолчанию
        self.set_title("Radio Player")
        self.set_default_icon(
        GdkPixbuf.Pixbuf.new_from_file(
        self.prog_full_path + '/resource/Radio32.png'))
        # Не менять размер
        self.set_resizable(False)
        # Ширина границ края основной формы
        self.set_border_width(5)
        # Установки позиции окна на экране по центру
        self.set_position(Gtk.WindowPosition.CENTER)
        self.set_type_hint(Gdk.WindowTypeHint.MENU)
        self.connect('key_press_event', self.on_key_press_event)
        self.window_state_on_desctop = 1
        #
        #@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

        # Список действующей настройки эквалайзера
        self.eq_set_preset = []

        # Если файл с адресами станций есть, то пропускаем
        if os.path.isfile(self.prog_full_path + '/adres_list.ini'):
            print('Файл с адресами найден ' + self.get_time_now())
        else:  # Если файл с адресами станций отсутствует то получаем его
            print('Файл с адресами создается ' + self.get_time_now())

            ad_101_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
            ad_101_opener.addheaders = [
                ('Host', '101.ru'),
                ('User-agent',
                'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

            # Запрос всех разделов
            with ad_101_opener.open('http://101.ru/?an=port_allchannels') as source_101_http:
                razdel_101_http = re.findall(
                r'<li class\="h4 tab\-item "><a href\="(.+?)">(.+?)<\/a><\/li>',
                source_101_http.read().decode('utf-8', errors='ignore'), re.M)

            dict_101_ru = []

            ## x = adr razdel, y = name razdel
            percent = len(razdel_101_http)
            check = 1
            for x, y in razdel_101_http:
                a = []
                with ad_101_opener.open('http://101.ru'+re.sub(r'amp;', r'', x, re.M)) as source_101_razdel:
                    source_101_http_razdel = re.findall(
                    r'<h2 class\="title"><a href\="(.+?)">(.+?)<\/a><\/h2>',
                    source_101_razdel.read().decode('utf-8', errors='ignore'), re.M)
                    for z, c in source_101_http_razdel:
                        a.append(c+' = '+re.sub(r'amp;', r'', z, re.M))
                    dict_101_ru.append(a)
                    sys.stdout.write("\r%d %%" % int(check//(percent/100)))
                    sys.stdout.flush()
                    check += 1

            final_conf = []
            for x in dict_101_ru:
                for d in x:
                    final_conf.append(d+'\n')

            with open(self.prog_full_path + '/adres_list.ini', 'w', encoding='utf-8', errors='ignore') as adr101file:
                adr101file.writelines(final_conf)

        with open(self.prog_full_path + '/adres_list.ini', 'r', encoding='utf-8', errors='ignore') as file_w:
            read_adr = file_w.readlines()

        self.read_list_adr = []

        for x in read_adr:
            self.read_list_adr.append(re.findall(r'(.+?)\s+=\s(.+?)\n', x, re.S))

        # Существуют ли записи в файле set-eq.ini предустановок эквалайзера или нет
        try:
            config = configparser.ConfigParser()
            config.read(self.prog_full_path + '/set-eq.ini', encoding='utf-8')
            leq = config['EQ-Settings']['lasteq'].split(' ')
            for x in leq:
                self.eq_set_preset.append(x)
        except KeyError:
            config = configparser.ConfigParser()
            config.add_section('EQ-Settings')
            config.set('EQ-Settings','lasteq','0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0')
            with open(self.prog_full_path + '/set-eq.ini', 'w') as cfgfile:
                config.write(cfgfile)
            config.read(self.prog_full_path + '/set-eq.ini', encoding='utf-8')
            leq = config['EQ-Settings']['lasteq'].split(' ')
            for x in leq:
                self.eq_set_preset.append(x)

        # Получение адреса потока 101 RU
        self.HURL = HackURL()

        # Запись последнего адреса потока
        self.wr_station_name_adr = WriteLastStation()

        # Объект Записи
        self.rec_obj = 0

        # Аббревиатуры каналов
        self.id_name_station = ['PS', 'My', 'DI', 'IRC', 'RREC', 'RTUN']

        # Статус Записи
        self.rec_status = False

        # Медиа данные (битрейт, моно или стерео)
        self.media_location = ''
        self.tooltip_now_text = ''

        # Отображается окно радио плеера или нет
        self.run_radio_window = 0
        # Уровень реальной громкости
        self.real_vol_save = 0

        # Играет радио или нет
        self.radio_play = 0
        # Играет радио или нет
        self.radio_rtmp_play = 0
        # Играет файл или нет
        self.file_play = 0

        # RMS чекер (отлов тишины)
        self.s_rms_chek = [0]

        # Таймеры
        self.timer = 0
        self.timer_title = 0
        self.timer_title_rtmp = 0
        self.timer_time = 0
        self.timer_rtun_title = 0

        # Контейнер для Gst.Pipeline
        self.pipeline = 0

        # Список хранящий плей лист
        self.f_name_len = []

        # Предел громкости для шкалы
        self.min_dcb = -45
        self.max_dcb = 0

        ## Иннфо канала
        # 0 = буквенное обозначение если не 101, если 101 то ID
        # 1 = адрес если не 101
        self.id_chan = [0,0]
        self.real_adress = '' # Адрес потока с контентом
        self.uri = [] # Список хранящий адреса на поток вещания
        self.My_ERROR_Mess = False # Чекер ошибок

        # Поиск cue файла
        self.cue_file_find = 0

        # Инфо ТАГ
        self.get_info_tag = [
        'organization',
        'header',
        'title',
        'artist',
        'album',
        'speed',
        'genre',
        'start-time',
        'end-time'
        ]

        self.tag_organization = ''

        ## Предустановки эквалайзера
        # Установки частот
        self.freq = [16,20,60,120,200,250,400,500,800,1000,2000,3000,4000,5000,6000,10000,12000,16000]
        # Установки ширины полосы частот
        self.bandwidth = [2, 2, 30, 40, 25, 75, 50, 150, 100, 500, 500, 500, 500, 500, 1000, 1000, 1000, 1000]
        # Предустановки эквалайзера
        self.equalizer_presets_dict = {
        'EQ Premaster': [0, 1, 3, 0, -3, -3, 0, 0, 0, 2, 0, 0, 3, 0, 3, 1, 3, 2],
        'EQ Soft Rock': [4, 5, 5, 5, 4, 3, 1, 0, -1, -2, -2, 0, 2, 3, 4, 5, 6, 7],
        'EQ Air': [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2],
        'EQ Techno 3': [6, 7, 7, 6, 4, 2, -1, -3, -2, 0, 2, 3, 4, 4, 4, 3, 2, 1],
        'EQ Pop 3': [6, 5, 3, 0, -2, -4, -4, -6, -3, 1, 0, 0, 2, 1, 2, 4, 5, 6],
        'EQ Disco': [3, 3, 1, 1, 3, 1, 1, 1, 2, 6, 5, 4, 3, 2, 2, 2, 2, 1],
        'EQ Latin': [0, -2, -1, 0, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 3, 2, 1, 1],
        'EQ Rock 2': [5, 4, 4, 3, 0, -4, -5, -5, -3, -2, 0, 1, 3, 4, 4, 5, 7, 8],
        'EQ Car Stereo': [-5, 0, 1, 0, 0, -4, -4, -5, -5, -5, -3, -2, -2, 0, 1, 0, -2, -5],
        'EQ Alt': [0, 1, 2, 2, 1, 0, 1, 0, 1, 1, 0, -1, -1, -1, -2, -1, 0, 1],
        'EQ Live': [-8, -2, 0, 0, 1, 1, 2, 4, 5, 5, 5, 4, 3, 1, 0, 0, 0, 1],
        'EQ Techno 2': [8, 8, 8, 6, 6, 3, 3, -3, -3, -2, -2, -2, 0, 4, 4, 5, 7, 7],
        'EQ Flat': [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        'EQ Chamber': [3, 2, -3, -5, -6, -5, -4, -5, -6, -7, -3, -1, 0, 0, 5, 5, 4, 3],
        'EQ Jazz': [0, 1, 2, 2, 3, 1, 2, 0, 0, 2, 1, 2, 4, 3, 3, 2, 1, 0],
        'EQ Paty': [7, 7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7],
        'EQ Line high up': [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 9, 14, 20],
        'EQ New Age': [3, 1, 3, 2, 2, 2, 3, 2, 0, 2, 4, 1, 3, 2, 4, 2, 1, 1],
        'EQ Soft Maniac': [0, -12, -7, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, -7, -12],
        'EQ Shimmer': [0, 0, 0, -2, -2, -7, -5, 0, 0, 0, 0, 0, 4, 1, 3, 3, 4, 0],
        'EQ Death': [20, 17, 12, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        'EQ Reggae': [0, 0, 0, -1, -3, -5, -8, -4, 0, 3, 4, 4, 4, 3, 1, 0, 0, 0],
        'EQ Strings': [-3, -4, -4, -5, -5, -4, -4, -3, -2, -2, -2, -2, -1, 2, 3, 0, -2, -2],
        'EQ Dark': [-6, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -5, -8, -10, -12, -14, -18, -18],
        'EQ Home Theater': [5, 2, 0, -2, -3, -5, -6, -6, -5, -2, -1, 0, -1, -3, 3, 4, 3, 0],
        'EQ 1965': [-20, -16, -7, -4, -4, -4, -7, -7, 3, 3, -2, -4, 4, 1, 1, -4, -6, -12],
        'EQ Bass': [3, 5, 4, 0, -13, -7, -5, -5, -1, 2, 5, 1, -1, -1, -2, -7, -9, -14],
        'EQ Dance 1': [11, 11, 8, 8, 8, 5, 5, 0, 0, 0, 0, -5, -5, -5, -8, -8, 0, 0],
        'EQ Rock 3': [7, 5, 3, 1, -2, -5, -6, -6, -5, -2, -1, 1, 2, 4, 8, 10, 15, 20],
        'EQ Pop 2': [-3, -3, -3, 3, 4, 6, 6, 6, 6, 3, 3, 3, -1, -1, -4, -4, -1, -1],
        'EQ Clear 1': [1, 1, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1],
        'EQ Soft 1': [3, 2, 0, 0, -1, -2, -2, 0, 2, 4, 5, 6, 7, 9, 9, 9, 10, 11],
        'EQ Punch & Sparkle': [3, 5, 3, -1, -3, -5, -5, -3, -2, 1, 1, 1, 0, 2, 1, 3, 5, 3],
        'EQ Bass&treble': [8, 7, 6, 4, 1, -2, -4, -3, 0, 2, 4, 6, 7, 8, 9, 9, 10, 10],
        'EQ Club': [0, 0, 0, 2, 2, 5, 5, 8, 8, 8, 8, 8, 8, 5, 5, 2, 0, 0],
        'EQ Pop 1': [1, -1, -3, 0, 1, 2, 3, 1, 1, 2, 0, -1, -2, 0, 1, 2, 2, 2],
        'EQ Heavy Metal': [4, 3, 2, 3, 6, 6, 6, 6, 6, 5, 4, 3, 3, 3, 2, 2, 2, 1],
        'EQ Metal': [4, 5, 5, 3, 0, -1, -2, -1, 0, 1, 1, 1, 1, 0, -1, -1, -1, -1],
        'EQ Dance 2': [14, 12, 10, 8, 6, 4, 4, 5, 5, 4, 1, 0, 0, 1, 3, 4, 5, 6],
        'EQ Brittle': [-12, -10, -9, -8, -7, -6, -5, -3, -2, -2, -2, -2, -1, 1, 4, 4, 1, 0],
        'EQ Techno 1': [3, 5, 3, 1, -1, 0, 1, 1, 2, 5, 3, 2, 5, 1, 2, 3, 4, 4],
        'EQ Vocal': [2, -1, -1, -1, 2, 2, 4, 3, 4, 4, 3, 2, 0, 0, 0, 0, -1, -1],
        'EQ Soft Bass': [3, 5, 4, 0, -13, -7, -5, -5, -1, 2, 5, 1, -1, -1, -2, -7, -9, -14],
        'EQ Classic V': [5, 2, 0, -2, -5, -6, -8, -8, -7, -7, -4, -3, -1, 1, 3, 5, 5, 4],
        'EQ Loudness': [4, 4, 4, 2, -2, -2, -2, -2, -2, -2, -2, -4, -10, -7, 0, 3, 4, 4],
        'EQ Acoustic': [3, 2, 2, 2, 3, 2, 2, 3, 2, 4, 2, 2, 1, 1, 4, 5, 7, 8],
        "EQ Drum'n'Bass": [3, 4, 3, 2, 2, 1, 0, 0, 1, 3, 5, 3, 2, 1, 2, 2, 1, 2],
        'EQ by Ekta': [2, 1, 0, -1, -3, -6, -8, -11, -11, -8, -6, -3, -1, 1, 3, 4, 5, 6],
        'EQ Rock 4': [12, 11, 9, 5, 0, -3, -3, 0, 3, 5, 6, 7, 8, 8, 9, 7, 8, 9],
        'EQ Pop 4': [1, 5, 8, 9, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0, 1, 0, 1, 2],
        'EQ Soft Heavy': [0, 7, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        'EQ Party': [7, 6, 5, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 5, 5],
        'EQ Rock 1': [3, -3, -2, -2, -2, -2, -2, -2, -1, -1, -1, -1, 0, 1, 2, 3, 4, 5],
        'EQ Presence': [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 4, 3, 2, 0, 0, 0, 0],
        'EQ Drums': [2, 1, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 2, 0, 0, 3, 0, 0],
        'EQ Clear 2': [0, -12, -7, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 7, 20],
        'EQ Classical': [3, 2, 1, 0, 2, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 1]}

        #!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        # RADIOTUNS
        #!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

        print('Получение адресов для RADIOTUNES ' + self.get_time_now())

        rtun_urls = []

        # Словарь для http://www.radiotunes.com/
        '''
        0   =   ID
        1   =   href
        2   =   name href
        3   =   name chanel
        '''
        self.rtun_dict_real_adr = {}

        self.rtun_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        self.rtun_opener.addheaders = [
        ('Host', 'www.radiotunes.com'),
        ('User-Agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

        with self.rtun_opener.open('http://www.radiotunes.com') as f:
            rtun_urls = re.findall(r'<li data\-channel\-id="(.+?)"> <span data\-event=".+?" data\-tunein\-url="(.+?)" class="play ui\-icon\-mini\_play"></span> <a href="/(.+?)"> <div class="channel\-icon\-\d+ channel\-icon.+?"></div> <span>(.+?)</span> </a> </li>', re.sub(r'&#x\d+;|amp;', r'', f.read().decode('utf-8')))

        for x in rtun_urls:
            self.rtun_dict_real_adr[x[3]] = x[0], x[1], x[2]

        self.rtun_liststore = Gtk.ListStore(str, bool)

        for x in sorted(self.rtun_dict_real_adr.keys()):
            self.rtun_liststore.append([x, False])

        self.rtun_treeview = Gtk.TreeView(model=self.rtun_liststore)
        self.rtun_treeview.set_enable_search(True)
        self.rtun_treeview.set_show_expanders(False)

        rtun_renderer_text = Gtk.CellRendererText()
        rtun_column_text = Gtk.TreeViewColumn("Станция", rtun_renderer_text, text=0)
        rtun_column_text.set_alignment(0.5)
        rtun_column_text.set_max_width(270)
        rtun_column_text.set_min_width(50)
        rtun_column_text.set_fixed_width(270)
        rtun_column_text.set_resizable(False)
        rtun_column_text.set_expand(False)
        self.rtun_treeview.append_column(rtun_column_text)

        rtun_renderer_radio = Gtk.CellRendererToggle()
        rtun_renderer_radio.set_radio(True)
        rtun_renderer_radio.connect("toggled", self.rtun_on_cell_radio_toggled)

        rtun_column_radio = Gtk.TreeViewColumn("Выбор", rtun_renderer_radio, active=1)
        rtun_column_radio.set_alignment(0.5)
        rtun_column_radio.set_resizable(False)
        rtun_column_radio.set_expand(False)
        self.rtun_treeview.append_column(rtun_column_radio)

        # Создание окна с прокруткой для размещения в нем List RadioTuns
        self.scrolled_window_rtun = Gtk.ScrolledWindow()
        self.scrolled_window_rtun.set_min_content_height(150)
        self.scrolled_window_rtun.set_min_content_width(340)
        self.scrolled_window_rtun.add(self.rtun_treeview)

        #'''# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        dinamit_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        dinamit_opener.addheaders = [
        ('Host', 'www.dfm.ru'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
        ]

        print('Получение адресов для DFM ' + self.get_time_now())
        with dinamit_opener.open('http://www.dfm.ru/listen/dfmonline/') as dinamit_http_source:
            dinamit_http_read_1 = dinamit_http_source.read().decode('utf-8', errors='ignore')

        dinamit_res = {x[1]:'http://www.dfm.ru'+x[0] for x in re.findall(r'<p><a href="(.+?)" title="Слушать.+?"><strong>(.+?)</strong>', dinamit_http_read_1, re.M)}

        self.d_fm_dict = dict()

        #
        def read_page(xarg, key):
            with dinamit_opener.open(xarg) as dinamit_http_source_2:
                dinamit_http_read = dinamit_http_source_2.read().decode('utf-8', errors='ignor')
                return (key, ''.join(re.findall(r'station\.player\.Html5Player\("(.+?)"', dinamit_http_read, re.M)))

        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            future_to_url = {executor.submit(read_page, val, key): val for key, val in dinamit_res.items()}
            for future in concurrent.futures.as_completed(future_to_url):
                try:
                    self.d_fm_dict[future.result()[0]] = future.result()[1]
                except Exception as exc:
                    print('%r generated an exception: %s' % (exc))
                else:
                    pass
        #
        '''## Словарь Ди-ФМ
            self.d_fm_dict = {'DFM Динамит': 'http://st16.fmtuner.ru',
            'ДИСКАЧ 90-х': 'http://st07.fmtuner.ru',
            'DFM Спокойной ночи, голыши!': 'http://st05.fmtuner.ru',
            'DFM 101,2': 'http://dfm.fmtuner.ru',
            'DFM  Deep': 'http://st24.fmtuner.ru',
            'DFM Club': 'http://st01.fmtuner.ru',
            'DFM Russian Dance': 'http://st03.fmtuner.ru'}'''

        self.di_grid = Gtk.Grid()

        # ЛистСтор для Тривью Ди-ФМ
        self.di_liststore = Gtk.ListStore(str, bool)
        for x in sorted(self.d_fm_dict):
            self.di_liststore.append([x, False])

        self.di_treeview = Gtk.TreeView(model=self.di_liststore)
        self.di_treeview.set_enable_search(True)
        self.di_treeview.set_show_expanders(False)

        di_renderer_text = Gtk.CellRendererText()
        di_column_text = Gtk.TreeViewColumn("Станция", di_renderer_text, text=0)
        di_column_text.set_alignment(0.5)
        di_column_text.set_max_width(270)
        di_column_text.set_min_width(50)
        di_column_text.set_fixed_width(270)
        di_column_text.set_resizable(False)
        di_column_text.set_expand(False)

        self.di_treeview.append_column(di_column_text)

        di_renderer_radio = Gtk.CellRendererToggle()
        di_renderer_radio.set_radio(True)
        di_renderer_radio.connect("toggled", self.di_on_cell_radio_toggled)

        di_column_radio = Gtk.TreeViewColumn("Выбор", di_renderer_radio, active=1)
        di_column_radio.set_alignment(0.5)
        di_column_radio.set_resizable(False)
        di_column_radio.set_expand(False)

        self.di_treeview.append_column(di_column_radio)

        self.di_grid.attach(self.di_treeview, 1, 1, 10, 12)
        self.di_grid.set_column_homogeneous(True)# Ровнять кнопки
        self.di_grid.set_row_homogeneous(False)
        self.di_grid.set_column_spacing(1)

        # Создание меню в трее
        self.main_menu = Gtk.Menu()

        # HIDE SHOW
        self.main_menu_items_hide = Gtk.MenuItem.new_with_label("Скрыть/Отобразить окно")
        self.main_menu.append(self.main_menu_items_hide)
        self.main_menu_items_hide.connect("activate", self.on_show_wed)
        self.main_menu_items_hide.show()

        # Gtk.SeparatorMenuItem1
        self.main_menu_separator_items_1 = Gtk.SeparatorMenuItem.new()
        self.main_menu.append(self.main_menu_separator_items_1)
        self.main_menu_separator_items_1.show()

        # Проиграть
        self.main_menu_items_play = Gtk.MenuItem.new_with_label("Воспроизвести")
        self.main_menu.append(self.main_menu_items_play)
        self.main_menu_items_play.connect("activate", self.on_click_bt1)
        self.main_menu_items_play.show()

        # Воспроизвести лучшую станцию
        self.main_menu_items_play_best_st = Gtk.MenuItem.new_with_label("Воспроизвести лучшую станцию")
        self.main_menu.append(self.main_menu_items_play_best_st)
        self.main_menu_items_play_best_st.connect("activate", self.on_play_best_st, 1)
        self.main_menu_items_play_best_st.show()

        # Воспроизвести последнюю станцию
        self.main_menu_items_play_last_st = Gtk.MenuItem.new_with_label("Воспроизвести последнюю станцию")
        self.main_menu.append(self.main_menu_items_play_last_st)
        self.main_menu_items_play_last_st.connect("activate", self.on_play_last_st, 1)
        self.main_menu_items_play_last_st.show()

        # Проиграть интернет адрес станции
        self.main_menu_items_play_m = Gtk.MenuItem.new_with_label("Воспроизвести пользовательский URL адрес")
        self.main_menu.append(self.main_menu_items_play_m)
        self.main_menu_items_play_m.connect("activate", self.on_dialog_choice)
        self.main_menu_items_play_m.show()

        # Пауза
        self.main_menu_items_pause = Gtk.MenuItem.new_with_label("Пауза")
        self.main_menu.append(self.main_menu_items_pause)
        self.main_menu_items_pause.connect("activate", self.on_click_bt4)
        self.main_menu_items_pause.show()

        # Стоп
        self.main_menu_items_stop = Gtk.MenuItem.new_with_label("Стоп")
        self.main_menu.append(self.main_menu_items_stop)
        self.main_menu_items_stop.connect("activate", self.on_click_bt5, self.main_menu_items_stop)
        self.main_menu_items_stop.show()

        # Gtk.SeparatorMenuItem2
        self.main_menu_separator_items_2 = Gtk.SeparatorMenuItem.new()
        self.main_menu.append(self.main_menu_separator_items_2)
        self.main_menu_separator_items_2.show()

        # Записать интернет адрес станции в мой плейлист
        self.main_menu_items_save_mpls = Gtk.MenuItem.new_with_label("Сохранить адрес в мой плейлист")
        self.main_menu.append(self.main_menu_items_save_mpls)
        self.main_menu_items_save_mpls.connect("activate", self.save_adres_in_pls)
        self.main_menu_items_save_mpls.show()

        # Сохранить лучшую станцию
        self.main_menu_items_write_best_st = Gtk.MenuItem.new_with_label("Сохранить лучшую станцию")
        self.main_menu.append(self.main_menu_items_write_best_st)
        self.main_menu_items_write_best_st.connect("activate", self.on_write_best_st, 0)
        self.main_menu_items_write_best_st.show()

        # Gtk.SeparatorMenuItem3
        self.main_menu_separator_items_3 = Gtk.SeparatorMenuItem.new()
        self.main_menu.append(self.main_menu_separator_items_3)
        self.main_menu_separator_items_3.show()

        # Поиск персональных станций
        self.main_menu_items_play_person = Gtk.MenuItem.new_with_label("Поиск персональных станций 101.ru")
        self.main_menu.append(self.main_menu_items_play_person)
        self.main_menu_items_play_person.connect("activate", self.search_in_personal_station)
        self.main_menu_items_play_person.show()

        # Обновить адресный лист
        self.main_menu_items_refresh_pl = Gtk.MenuItem.new_with_label("Обновить адресный лист 101.ru")
        self.main_menu.append(self.main_menu_items_refresh_pl)
        self.main_menu_items_refresh_pl.connect("activate", self.on_refresh_list)
        self.main_menu_items_refresh_pl.show()

        # Gtk.SeparatorMenuItem4
        self.main_menu_separator_items_4 = Gtk.SeparatorMenuItem.new()
        self.main_menu.append(self.main_menu_separator_items_4)
        self.main_menu_separator_items_4.show()

        self.vol_menu = Gtk.Menu()

        # Громкость
        self.main_menu_items_vol = Gtk.MenuItem.new_with_label("Громкость")
        self.main_menu_items_vol.set_submenu(self.vol_menu)
        self.main_menu.append(self.main_menu_items_vol)
        self.main_menu_items_vol.show()
        for x in range(0, 105, 5):
            self.vol_menu.append(Gtk.CheckMenuItem.new_with_label(str(x)))
        for x in self.vol_menu:
            x.connect("activate", self.on_togled_menu_it, 'B')
            x.show()

        self.eq_menu = Gtk.Menu()

        # Подменю Эквалайзера
        self.main_menu_items_eq = Gtk.MenuItem.new_with_label("Эквалайзер")
        self.main_menu_items_eq.set_submenu(self.eq_menu)

        # Редактировать пользовательские пресеты эквалайзера
        self.eq_menu_items_eq_edit = Gtk.MenuItem.new_with_label("Редактировать положение эквалайзера")
        self.eq_menu.append(self.eq_menu_items_eq_edit)
        self.eq_menu_items_eq_edit.connect("activate", self.edit_eq)
        self.eq_menu_items_eq_edit.show()

        # Установки именованных настроек эквалайзера
        for x in sorted(self.equalizer_presets_dict):
            self.eq_menu.append(Gtk.MenuItem.new_with_label(str(x)))
        for x in self.eq_menu:
            x.connect("activate", self.change_equlaizer, x.get_label())
            x.show()
        self.main_menu.append(self.main_menu_items_eq)
        self.main_menu_items_eq.show()

        # Gtk.SeparatorMenuItem5
        self.main_menu_separator_items_5 = Gtk.SeparatorMenuItem.new()
        self.main_menu.append(self.main_menu_separator_items_5)
        self.main_menu_separator_items_5.show()

        # Выход
        self.main_menu_items_quit = Gtk.MenuItem.new_with_label("Выход")
        self.main_menu.append(self.main_menu_items_quit)
        self.main_menu_items_quit.connect("activate", Gtk.main_quit)
        self.main_menu_items_quit.show()

        # О Программе
        self.main_menu_items_about = Gtk.MenuItem.new_with_label("О Программе")
        self.main_menu.append(self.main_menu_items_about)
        self.main_menu_items_about.connect("activate", self.dialog_about)
        self.main_menu_items_about.show()

        print('Создание AppIndicator3 ' + self.get_time_now())

        # Создание иконки/меню в трее
        if APP_INDICATOR:
            self.tray_icon = AppIndicator3.Indicator.new(
            'Radio Player',
            self.prog_full_path + '/resource/Radio24.png',
            AppIndicator3.IndicatorCategory.APPLICATION_STATUS)

            self.tray_icon.set_status (AppIndicator3.IndicatorStatus.ACTIVE)
            self.tray_icon.set_title('Radio Player')
            self.tray_icon.set_menu(self.main_menu)
        else:
            self.tray_icon = Gtk.StatusIcon()
            self.tray_icon.connect('button-release-event', self.create_main_menu)
            self.tray_icon.set_tooltip_text("Radio Player")
            self.tray_icon.set_from_file(self.prog_full_path + '/resource/Radio32.png')
            self.tray_icon.set_visible(True)

        # Создание List с именами всех станций 101 RU
        self.liststore_101 = Gtk.ListStore(str, bool)
        for x in self.read_list_adr:
            self.liststore_101.append([str(x[0][0]), False])

        # Создание TreeView 101
        self.treeview_101 = Gtk.TreeView(model=self.liststore_101)
        self.treeview_101.connect("button-press-event", self.button_press)

        # Создание столбца "Станция"
        renderer_text = Gtk.CellRendererText()

        self.column_text_101 = Gtk.TreeViewColumn("Станция", renderer_text, text=0)
        self.column_text_101.set_alignment(0.5)
        self.column_text_101.set_max_width(270)
        self.column_text_101.set_min_width(50)
        self.column_text_101.set_fixed_width(270)
        self.column_text_101.set_resizable(False)
        self.column_text_101.set_expand(False)

        self.treeview_101.append_column(self.column_text_101)

        renderer_radio_101 = Gtk.CellRendererToggle()
        renderer_radio_101.set_radio(True)
        renderer_radio_101.connect("toggled", self.on_cell_radio_toggled)

        # Создание столбца "Выбор"
        column_radio_101 = Gtk.TreeViewColumn("Выбор", renderer_radio_101, active=1)
        column_radio_101.set_alignment(0.5)
        column_radio_101.set_resizable(False)
        column_radio_101.set_expand(False)
        self.treeview_101.append_column(column_radio_101)

        # Создание сетки для размещения Internet Radio COM
        self.grid_for_IRC = Gtk.Grid.new()

        self.RIC_url = ''

        self.loc_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
        self.loc_config.read(self.prog_full_path + '/radiointernet.txt', encoding = 'utf-8')
        self.c_s = self.loc_config.sections()

        if len(self.c_s) == 0:
            self.w_grid = Gtk.Grid()
            self.w_grid.set_border_width(5)
            self.w_label = Gtk.Label('Файл с адресами Internet Radio COM не найден!')
            self.w_label.modify_bg(Gtk.StateType.NORMAL, Gdk.Color.from_floats(1.0, 0.2, 0.0))
            self.w_batton1 = Gtk.Button('Создать стандартный файл адресов')
            self.w_batton1.connect('clicked', self.create_irc_list, 1)
            self.w_batton2 = Gtk.Button('Создать расширенный файл адресов')
            self.w_batton2.connect('clicked', self.create_irc_list, 2)
            self.w_grid.attach(self.w_label, 1, 1, 5, 1)
            self.w_grid.attach(self.w_batton1, 1, 2, 5, 1)
            self.w_grid.attach(self.w_batton2, 1, 3, 5, 1)
            self.w_grid.set_column_homogeneous(True)# Ровнять
            self.w_grid.set_row_homogeneous(True)
            self.w_grid.set_column_spacing(1)
        else:
            self.liststore_RIC = Gtk.ListStore(str, bool)
            for x in self.c_s:
                self.liststore_RIC.append([x, False])

            self.top_treeview = Gtk.TreeView(model=self.liststore_RIC)
            self.top_treeview.set_tooltip_column(0)
            self.top_treeview.set_enable_search(True)
            self.top_treeview.set_show_expanders(False)

            self.top_renderer_text = Gtk.CellRendererText()
            self.top_column_text = Gtk.TreeViewColumn("Раздел", self.top_renderer_text, text=0)
            self.top_column_text.set_alignment(0.5)
            self.top_column_text.set_max_width(270)
            self.top_column_text.set_min_width(50)
            self.top_column_text.set_fixed_width(270)
            self.top_column_text.set_resizable(False)
            self.top_column_text.set_expand(False)

            self.top_treeview.append_column(self.top_column_text)

            self.top_renderer_radio = Gtk.CellRendererToggle()
            self.top_renderer_radio.set_radio(True)
            self.top_renderer_radio.connect("toggled", self.on_cell_radio_toggled_RIC)

            self.top_column_radio = Gtk.TreeViewColumn("Выбор", self.top_renderer_radio, active=1)
            self.top_column_radio.set_alignment(0.5)
            self.top_column_radio.set_expand(False)
            self.top_column_radio.set_resizable(False)
            self.top_treeview.append_column(self.top_column_radio)

        self.liststore_sub = Gtk.ListStore(str, bool)

        self.sub_treeview = Gtk.TreeView(model=self.liststore_sub)
        self.sub_treeview.set_tooltip_column(0)
        self.sub_treeview.set_enable_search(True)
        self.sub_treeview.set_show_expanders(False)

        sub_renderer_text = Gtk.CellRendererText()

        sub_column_text = Gtk.TreeViewColumn("Станция", sub_renderer_text, text=0)
        sub_column_text.set_alignment(0.5)
        sub_column_text.set_max_width(270)
        sub_column_text.set_min_width(50)
        sub_column_text.set_fixed_width(270)
        sub_column_text.set_resizable(False)
        sub_column_text.set_expand(False)

        sub_column_text.set_max_width(270)
        sub_column_text.set_min_width(50)
        sub_column_text.set_fixed_width(270)
        sub_column_text.set_resizable(False)
        self.sub_treeview.append_column(sub_column_text)

        sub_renderer_radio = Gtk.CellRendererToggle()
        sub_renderer_radio.set_radio(True)
        sub_renderer_radio.connect("toggled", self.on_cell_radio_toggled_s_RIC)

        sub_column_radio = Gtk.TreeViewColumn("Выбор", sub_renderer_radio, active=1)
        sub_column_radio.set_alignment(0.5)
        sub_column_radio.set_resizable(False)
        sub_column_radio.set_expand(False)

        self.sub_treeview.append_column(sub_column_radio)

        # Создание окна с прокруткой для размещения в нем List 101
        self.scrolled_window_101 = Gtk.ScrolledWindow()
        self.scrolled_window_101.set_min_content_height(150)
        self.scrolled_window_101.set_min_content_width(340)
        self.scrolled_window_101.add(self.treeview_101)

        # Создание окна с прокруткой для размещения в нем List Di-FM
        self.di_scrolled_window = Gtk.ScrolledWindow()
        self.di_scrolled_window.set_min_content_height(150)
        self.di_scrolled_window.set_min_content_width(340)
        self.di_scrolled_window.add(self.di_grid)

        # Создание окна с прокруткой для размещения в нем Radio Internet
        self.top_window = Gtk.ScrolledWindow()
        self.top_window.set_min_content_height(150)
        self.top_window.set_min_content_width(340)
        if len(self.c_s) == 0:
            self.top_window.add(self.w_grid)
        else:
            self.top_window.add(self.top_treeview)

        # Создание окна с прокруткой для размещения в нем Radio Internet
        self.sub_window = Gtk.ScrolledWindow()
        self.sub_window.set_min_content_height(150)
        self.sub_window.set_min_content_width(340)
        self.sub_window.add(self.sub_treeview)

        self.grid_for_IRC.attach(self.top_window, 1, 1, 10, 6)
        self.grid_for_IRC.attach(self.sub_window, 1, 7, 10, 6)

        self.grid_for_IRC.set_column_homogeneous(True)# Ровнять
        self.grid_for_IRC.set_row_homogeneous(False)
        self.grid_for_IRC.set_column_spacing(1)

        # Радио рекорд
        record_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        record_opener.addheaders = [
        ('Host', 'www.radiorecord.ru'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
        ]

        try:
            with record_opener.open('http://www.radiorecord.ru/player/') as http_source:
                http_read = http_source.read().decode('utf-8', errors='ignore')
            record_res = re.findall(r'<div class="station".+?class="station-name">(.+?)</div><div class="station-track">.+?itemprop="url">(.+?)</div></div>', http_read, re.M)

            self.record_dict = {x[0]:x[1] for x in record_res}
        except:
            self.record_dict = {
            "Pump'n'Klubb": 'http://air.radiorecord.ru:8102/pump_320',
            'Rock Radio': 'http://air.radiorecord.ru:8102/rock_320',
            'Супердискотека 90-х': 'http://air.radiorecord.ru:8102/sd90_320',
            'Radio Record': 'http://air.radiorecord.ru:8101/rr_320',
            'Record Chill-Out': 'http://air.radiorecord.ru:8102/chil_320',
            'Record Dubstep': 'http://air.radiorecord.ru:8102/dub_320',
            'Pirate Station': 'http://air.radiorecord.ru:8102/ps_320',
            'Vip Mix': 'http://air.radiorecord.ru:8102/vip_320',
            'Record Club': 'http://air.radiorecord.ru:8102/club_320',
            'Record Breaks': 'http://air.radiorecord.ru:8102/brks_320',
            'Russian Mix': 'http://air.radiorecord.ru:8102/rus_320',
            'Record Trap': 'http://air.radiorecord.ru:8102/trap_320',
            'Record Hardstyle': 'http://air.radiorecord.ru:8102/teo_320',
            'Record Deep': 'http://air.radiorecord.ru:8102/deep_320',
            'Медляк FM': 'http://air.radiorecord.ru:8102/mdl_320',
            'Record Dancecore': 'http://air.radiorecord.ru:8102/dc_320',
            'Trancemission': 'http://air.radiorecord.ru:8102/tm_320',
            'Гоп FM': 'http://air.radiorecord.ru:8102/gop_320'}

        self.record_liststore = Gtk.ListStore(str, bool, bool)
        for x in sorted(self.record_dict):
            self.record_liststore.append([x, False, False])

        self.record_treeview = Gtk.TreeView(model=self.record_liststore)
        self.record_treeview.set_tooltip_column(0)
        self.record_treeview.set_enable_search(True)
        self.record_treeview.set_show_expanders(False)

        self.record_renderer_text = Gtk.CellRendererText()
        self.record_column_text = Gtk.TreeViewColumn("Станция", self.record_renderer_text, text=0)
        self.record_column_text.set_alignment(0.5)
        self.record_column_text.set_max_width(270)
        self.record_column_text.set_min_width(50)
        self.record_column_text.set_fixed_width(270)
        self.record_column_text.set_resizable(False)
        self.record_column_text.set_expand(False)

        self.record_treeview.append_column(self.record_column_text)

        self.record_renderer_radio = Gtk.CellRendererToggle()
        self.record_renderer_radio.set_radio(True)
        self.record_renderer_radio.connect("toggled", self.record_on_cell_radio_toggled)

        self.record_column_radio = Gtk.TreeViewColumn("Выбор", self.record_renderer_radio, active=1)
        self.record_column_radio.set_alignment(0.5)
        self.record_column_radio.set_resizable(False)
        self.record_column_radio.set_expand(False)
        self.record_treeview.append_column(self.record_column_radio)

        self.record_scrolled_window = Gtk.ScrolledWindow()
        self.record_scrolled_window.set_min_content_height(150)
        self.record_scrolled_window.set_min_content_width(340)
        self.record_scrolled_window.add(self.record_treeview)

        # My Play List
        self.my_pls_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
        self.my_pls_config.read(self.prog_full_path + '/my_pls.ini')

        self.my_pls_liststore = Gtk.ListStore(str, bool)
        for x in sorted(self.my_pls_config.sections()):
            self.my_pls_liststore.append([x, False])

        self.my_pls_treeview = Gtk.TreeView(model=self.my_pls_liststore)
        self.my_pls_treeview.connect("button-release-event", self.menu_del_line)
        self.my_pls_treeview.set_tooltip_column(0)
        self.my_pls_treeview.set_enable_search(True)
        self.my_pls_treeview.set_show_expanders(False)

        self.my_pls_renderer_text = Gtk.CellRendererText()
        self.my_pls_column_text = Gtk.TreeViewColumn("Станция", self.my_pls_renderer_text, text=0)
        self.my_pls_column_text.set_alignment(0.5)
        self.my_pls_column_text.set_max_width(270)
        self.my_pls_column_text.set_min_width(50)
        self.my_pls_column_text.set_fixed_width(270)
        self.my_pls_column_text.set_resizable(False)
        self.my_pls_column_text.set_expand(False)

        self.my_pls_treeview.append_column(self.my_pls_column_text)

        self.my_pls_renderer_radio = Gtk.CellRendererToggle()
        self.my_pls_renderer_radio.set_radio(True)
        self.my_pls_renderer_radio.connect("toggled", self.my_pls_on_cell_radio_toggled)

        self.my_pls_column_radio = Gtk.TreeViewColumn("Выбор", self.my_pls_renderer_radio, active=1)
        self.my_pls_column_radio.set_alignment(0.5)
        self.my_pls_column_radio.set_resizable(False)
        self.my_pls_column_radio.set_expand(False)
        self.my_pls_treeview.append_column(self.my_pls_column_radio)

        self.my_pls_scrolled_window = Gtk.ScrolledWindow()
        self.my_pls_scrolled_window.add(self.my_pls_treeview)
        self.my_pls_scrolled_window.set_min_content_height(300)
        self.my_pls_scrolled_window.set_min_content_width(340)
        self.my_pls_scrolled_window.set_size_request(300, 300)

        # Создание табов для порталов
        self.main_note_for_cont = Gtk.Notebook()
        self.main_note_for_cont.set_border_width(5)
        self.main_note_for_cont.set_scrollable(True)
        self.main_note_for_cont.set_property('expand', False)
        self.main_note_for_cont.set_property('enable-popup', True)
        self.main_note_for_cont.set_property('show-border', False)

        # Добавление табов с порталами
        self.main_note_for_cont.append_page(self.scrolled_window_101, Gtk.Label('Radio 101'))
        self.main_note_for_cont.append_page(self.di_scrolled_window, Gtk.Label('Radio Di-FM'))
        self.main_note_for_cont.append_page(self.grid_for_IRC, Gtk.Label('Internet Radio'))
        self.main_note_for_cont.append_page(self.record_scrolled_window, Gtk.Label('Radio Record'))
        self.main_note_for_cont.append_page(self.scrolled_window_rtun, Gtk.Label('RadioTuns'))
        self.main_note_for_cont.append_page(self.my_pls_scrolled_window, Gtk.Label('My Play List'))

        # Создание кнопки громкости
        self.scal_sl = Gtk.VolumeButton()
        self.scal_sl.set_hexpand_set(True)
        self.scal_sl.set_adjustment(Gtk.Adjustment.new(0.50, 0.00, 1.00, 0.01, 0.02, 0.01))
        self.scal_sl.set_relief(2)
        self.scal_sl.set_border_width(5)
        self.scal_sl.connect("value-changed", self.on_valu_ch)

        ## Создание левого и правого "Эквалайзеров"
        self.level_bar_l = Gtk.ProgressBar.new()
        self.level_bar_l.set_show_text(False)
        self.level_bar_l.set_inverted(True)
        self.level_bar_l.set_orientation(Gtk.Orientation.VERTICAL)
        self.level_bar_r = Gtk.ProgressBar.new()
        self.level_bar_r.set_show_text(False)
        self.level_bar_r.set_inverted(True)
        self.level_bar_r.set_orientation(Gtk.Orientation.VERTICAL)

        # Создание кнопок (воспроизведение, открыть файл, открыть папку, пауза, стоп)
        self.button_array = []
        self.button_tooltip = [
        'Воспроизведение',
        'Воспроизвести файл',
        'Воспроизвести директорию',
        'Пауза',
        'Стоп',
        'Запись'
        ]
        self.button_actions = [
        self.on_click_bt1,
        self.on_click_bt2,
        self.on_click_bt3,
        self.on_click_bt4,
        self.on_click_bt5,
        self.on_click_bt6
        ]
        self.img_for_button_array = []
        self.button_img_array = [
        Gtk.STOCK_MEDIA_PLAY,
        Gtk.STOCK_FILE,
        Gtk.STOCK_DIRECTORY,
        Gtk.STOCK_MEDIA_PAUSE,
        Gtk.STOCK_MEDIA_STOP,
        Gtk.STOCK_MEDIA_RECORD]
        for x in range(6):
            self.img_for_button_array.append(Gtk.Image())
            self.img_for_button_array[x].set_from_stock(self.button_img_array[x], 4)

            self.button_array.append(Gtk.Button(use_stock=True))
            self.button_array[x].set_image(self.img_for_button_array[x])
            self.button_array[x].set_relief(Gtk.ReliefStyle.NONE)
            self.button_array[x].set_resize_mode(Gtk.ResizeMode.PARENT)
            self.button_array[x].set_alignment(0.5, 0.5)
            self.button_array[x].set_tooltip_text(self.button_tooltip[x])
            self.button_array[x].connect("clicked", self.button_actions[x])

        # Создание лейбла для отображения названия
        self.label_title = Gtk.Label()
        self.label_title.set_line_wrap(True)
        self.label_title.set_line_wrap_mode(Pango.WrapMode.WORD)
        self.label_title.set_width_chars(50)
        self.label_title.set_selectable(True)
        self.label_title.set_justify(Gtk.Justification.CENTER)
        self.label_title.modify_font(Pango.FontDescription("9"))

        # Создание лейбла для отображения продолжительности
        self.label_time = Gtk.Label('00:00:00:00')
        self.label_time.set_selectable(True)
        self.label_time.set_justify(Gtk.Justification.LEFT)
        self.label_time.modify_font(Pango.FontDescription("10"))

        # Создание лейбла для отображения общей длительности
        self.label_ltime = Gtk.Label('00:00:00:00')
        self.label_ltime.set_selectable(True)
        self.label_ltime.set_justify(Gtk.Justification.LEFT)
        self.label_ltime.modify_font(Pango.FontDescription("10"))

        # Создание лейбла для отображения состояния моно или стерео
        self.label_mon_st = Gtk.Label('MediaInfo')
        self.label_mon_st.set_has_tooltip(True)
        self.label_mon_st.connect("query-tooltip", self.media_tool_hint)
        self.label_mon_st.set_justify(Gtk.Justification.CENTER)
        self.label_mon_st.modify_font(Pango.FontDescription("9"))
        self.label_mon_st.modify_font(Pango.FontDescription('bold'))
        self.label_mon_st.set_max_width_chars(10)

        ## Создание прогресса для отображения положения звучания
        # Ползунок воспроизведения
        self.seek_line = Gtk.HScale.new_with_range(0, 100, 0.01)
        self.seek_line.set_draw_value(False)
        self.seek_line.set_digits(2)
        self.seek_line.connect('button-release-event', self.new_seek_pos_set)
        self.seek_line.connect('button-press-event', self.popup_for_cue_on_seek_line)

        # Создание плейлиста
        #
        self.playlist_liststore = Gtk.ListStore(str, str)

        self.playlist_liststore.append([None, None])

        self.playlist_treeview = Gtk.TreeView(model=self.playlist_liststore)
        self.playlist_treeview.connect('row_activated', self.click_to_row_pl)

        self.playlist_renderer_pixbuf = Gtk.CellRendererPixbuf()
        self.playlist_column_pixbuf = Gtk.TreeViewColumn('♫', self.playlist_renderer_pixbuf, stock_id=0)
        self.playlist_treeview.append_column(self.playlist_column_pixbuf)

        self.playlist_renderer_text = Gtk.CellRendererText()
        self.playlist_column_text = Gtk.TreeViewColumn('Title', self.playlist_renderer_text, text=1)
        self.playlist_treeview.append_column(self.playlist_column_text)

        self.playlist_scrolled_window = Gtk.ScrolledWindow()
        self.playlist_scrolled_window.set_min_content_height(150)
        self.playlist_scrolled_window.set_min_content_width(340)
        self.playlist_scrolled_window.add(self.playlist_treeview)
        #

        # Первая (основная сетка размещения)
        self.grid = Gtk.Grid()
        self.grid.set_border_width(5)

        # Вторая сетка размещения для кнопок
        self.grid_button = Gtk.Grid()
        self.grid_button.set_border_width(5)

        # Создание сетки с кнопками
        self.grid_button.attach(self.button_array[0], 1, 1, 1, 1)
        for x in range(1, 6):
            self.grid_button.attach_next_to(self.button_array[x], self.button_array[x-1], Gtk.PositionType.RIGHT, 1, 1)

        # Помещение сетки с кнопками в основную сетку
        self.grid.attach(self.grid_button, 1, 1, 5, 1)# Разместить сетку с кнопками

        # Помещение табов в основную сетку
        self.grid.attach(self.main_note_for_cont, 1, 2, 5, 4)# Окно со станциями
        self.grid.attach(self.label_time,  1, 6, 1, 1)# Лейбл времени L
        self.grid.attach(self.label_title, 1, 7, 5, 1)# Лейбл названия
        self.grid.attach(self.scal_sl,     2, 6, 3, 1)# Регулятор громкости
        self.grid.attach(self.label_ltime, 5, 6, 1, 1)# Лейбл времени R

        self.grid.attach(self.label_mon_st, 0, 8, 7, 1)# Лейбл медиаинфо

        self.grid.attach(self.seek_line, 0, 9, 7, 1)# Лейбл прогресса звучания

        # Помещение эквалайзеров в основную сетку
        self.grid.attach(self.level_bar_l, 0, 1, 1, 5)# Шкала громкости
        self.grid.attach(self.level_bar_r, 6, 1, 1, 5)# Шкала громкости

        self.grid.attach(self.playlist_scrolled_window, 1, 10, 5, 1)# Плейлист

        self.grid_button.set_column_homogeneous(True)# Ровнять кнопки
        self.grid_button.set_row_homogeneous(False)
        self.grid_button.set_column_spacing(1)

        self.grid.set_column_homogeneous(False)# Не ровнять основную сетку
        self.grid.set_row_homogeneous(False)
        self.grid.set_column_spacing(1)
        self.add(self.grid)
        print('Сетка размещения создана ' + self.get_time_now())

        #^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^#
        ###################################################
        ###################################################
        ###################################################
        ###################################################
        ###################################################
        ###################################################

    # Возвращение адреса на поток RADIOTUNES
    def rtunes_stream_url(self, key):

        r_key = key
        req = 'http://listen.radiotunes.com/webplayer/' + r_key + '.jsonp?callback=_API_Playlists_getChannel'
        try:
            self.rtun_opener.addheaders = [('Host', 'listen.radiotunes.com')]
            with self.rtun_opener.open(req) as conn:
                ans = re.findall(r'"(.+?)"', re.sub(r'\\', r'', conn.read().decode('utf-8')))
                return ans[0]
        except HTTPError as e:
            print('HTTPError The server ' + r_key + ' couldn\'t fulfill the request.', e.code)
            return False
        except URLError as e:
            print('URLError We failed to reach a ' + r_key + ' server.', e.reason)
            return False
    #

    # Обработка событий RadioTuns
    def rtun_on_cell_radio_toggled(self, widget, path):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            source_cell = self.rtun_liststore.get_iter(path)
            for x in self.rtun_dict_real_adr.keys():
                if x == self.rtun_liststore.get_value(source_cell, 0):
                    self.id_chan = ['RTUN', re.sub(r'\_aacplus\.flv', r'', str(self.rtun_dict_real_adr[x]))]
                    get_adr_rtunes = self.rtunes_stream_url(self.rtun_dict_real_adr[x][2])
                    print(get_adr_rtunes, self.rtun_dict_real_adr[x])
                    if get_adr_rtunes != False:
                        self.real_adress = re.sub(r'\_aacplus\.flv', r'', get_adr_rtunes)
                    else:
                        return False

            for row in self.rtun_liststore:
                row[1] = (row.path == selected_path)

    # Обработка событий плейлиста
    def click_to_row_pl(self, tree_view, path, column):

        if self.pipeline:
            self.pipeline.set_state(Gst.State.NULL)
            self.pipeline = 0

        file_name_from_pl = ''

        #c = self.playlist_liststore.get_iter(path)
        i = path.get_indices()[0]

        for x in range(len(self.playlist_liststore)):
            self.playlist_liststore.set_value(self.playlist_liststore.get_iter(x), 0, None)

        for x in range(len(self.playlist_liststore)):
            if i == x:
                self.playlist_liststore.set_value(self.playlist_liststore.get_iter(x), 0, Gtk.STOCK_MEDIA_PLAY)
                file_name_from_pl = self.playlist_liststore.get_value(self.playlist_liststore.get_iter(x), 1)
                for x in range(x, len(self.playlist_liststore)):
                    self.f_name_len.append(self.playlist_file[x])
        self.id_chan = ['file', 0]
        self.play_stat_now(self.playlist_dict[file_name_from_pl])

    # Возвращение реального времени
    def get_time_now(self):

        return str(datetime.datetime.now().strftime('%H:%M:%S'))

    # Установка галочки на меню громкости
    def on_togled_menu_it(self, check_menu_item, args):

        #if self.pipeline and args == 'B':
        if args == 'B':
            c = 0
            for x in self.vol_menu:
                if x.get_active():
                    c += 1
            if c > 1:
                for x in self.vol_menu:
                    if x.get_active() and x != check_menu_item:
                        x.set_active(False)
            self.on_valu_ch(check_menu_item, int(check_menu_item.get_label())/100, 'A')

    # Cкрыть окно по нажатию Escape
    def on_key_press_event(self, widget, event):

        keyname = Gdk.keyval_name(event.keyval)
        if 'Escape' == keyname:
            self.hide()

    # Отобразить/скрыть окно
    def on_show_wed(self, *args):

        if self.window_state_on_desctop:
            self.hide()
            self.window_state_on_desctop = 0
            return True
        else:
            self.window_state_on_desctop = 1
            self.show()

        if self.file_play == 1:
            # Отобразить SeekLine
            self.seek_line.show()
            self.playlist_scrolled_window.show()
            # Скрыть Notebook
            self.main_note_for_cont.hide()
            for x in range(6):
                if x != 3 and x != 4 and x != 5:
                    self.button_array[x].hide()
                else:
                    self.button_array[x].show()
        if self.radio_play == 1 or self.radio_rtmp_play == 1:
            self.seek_line.hide()
            self.playlist_scrolled_window.hide()
            for x in range(6):
                if x != 3 and x != 4 and x != 5:
                    self.button_array[x].hide()
                else:
                    self.button_array[x].show()
        if self.radio_play != 1 and self.radio_rtmp_play != 1 and self.file_play != 1:
            if self.file_play == 0:
                self.seek_line.hide()
                self.playlist_scrolled_window.hide()
                for x in range(6):
                    if x == 5:
                        self.button_array[x].hide()

    # Распознать кодировку
    def lang_ident_str(self, get_text):

        lang_ident = ''
        b = []

        for x in get_text:
            if ord(x):
                b.append(ord(x))

        try:
            if max(b) > 256 and max(b) < 2000:
                #print('1 MAX', max(b), min(b))
                #lang_ident = 'Ru'
                return get_text.encode('cp1251', errors='ignore').decode('cp1251', errors='ignore')
            elif max(b) > 2000:
                #print('2 MAX', max(b), min(b))
                #lang_ident = 'Ru'
                try:
                    return get_text.encode('cp1251').decode('utf-8')
                except:
                    return get_text.encode('cp1251').decode('cp1251')
            elif max(b) < 129 and min(b) < 129:
                #print('3 MAX', max(b), min(b))
                #lang_ident = 'En'
                return get_text.encode('utf_8', errors='ignore').decode('utf-8', errors='ignore')
            elif max(b) < 256 and min(b) < 256:
                #print('4 MAX', max(b), min(b))
                #lang_ident = 'EnRu'
                try:
                    return get_text.encode('latin-1').decode('utf-8')
                except:
                    return get_text.encode('latin-1').decode('cp1251')
        except ValueError:
            return False

    # Удаление строки из моего плейлиста
    def n_next(self, *args):

        self.del_my_pls_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
        self.del_my_pls_config.read(self.prog_full_path + '/my_pls.ini')

        for x in self.del_my_pls_config.sections():
            if x == args[1]:
                print('Удаление записи адреса из моего плейлиста ==> ', args[1])
                self.del_my_pls_config.remove_section(args[1])

        with open(self.prog_full_path + '/my_pls.ini', 'w') as configfile:
            self.del_my_pls_config.write(configfile)

        self.my_pls_liststore.clear()

        for x in sorted(self.del_my_pls_config.sections()):
            self.my_pls_liststore.append([x, False])

    # Удаление записи из моего листа
    def menu_del_line(self, widget, event):

        d = self.my_pls_liststore.get_value(self.my_pls_liststore.get_iter(widget.get_cursor()[0]), 0)

        if event.button == 3:
            self.menu_pop_show = Gtk.Menu()
            self.menu_copy = Gtk.MenuItem("Удалить")
            self.menu_copy.connect('activate', self.n_next, d)
            self.menu_pop_show.append(self.menu_copy)
            self.menu_pop_show.show_all()
            self.menu_pop_show.popup(None, None, None, None, event.button, event.get_time())

    ## Pop-up menu for 101 RU
    # Обновление плейлиста
    def button_press(self, widget, event):

        if event.button == 3:
            self.menu_pop_show = Gtk.Menu()
            self.menu_copy = Gtk.MenuItem("Обновить")
            self.menu_copy.connect('activate', self.on_refresh_list)
            self.menu_pop_show.append(self.menu_copy)
            self.menu_pop_show.show_all()
            self.menu_pop_show.popup(None, None, None, None, event.button, event.get_time())

    # Диалог о программе
    def dialog_about(self, widget):

        about = Gtk.AboutDialog()
        about.set_transient_for(self)
        about.set_program_name("Internet Radio Player")
        about.set_version(SCRIPT_VERSION)
        about.set_copyright("(c) IvSatel 2015")
        about.set_comments("Internet Radio Player")
        about.set_logo(GdkPixbuf.Pixbuf.new_from_file_at_size(self.prog_full_path + '/resource/Radio256.png', 256, 256))
        about.run()
        about.destroy()

    # Реакция на сохранение в окне MyPLS
    def save_adres_in_pls(self, *args):

        self.my_pls_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
        self.my_pls_config.read(self.prog_full_path + '/my_pls.ini')
        print('Запись адреса в мой плейлист ==> ', self.tag_organization, self.real_adress)
        self.my_pls_config.add_section(self.tag_organization)
        self.my_pls_config.set(self.tag_organization, 'addrstation', self.real_adress)
        with open(self.prog_full_path + '/my_pls.ini', 'w') as configfile:
            self.my_pls_config.write(configfile)

        self.my_pls_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
        self.my_pls_config.read(self.prog_full_path + '/my_pls.ini')

        self.my_pls_liststore.clear()

        for x in sorted(self.my_pls_config.sections()):
            self.my_pls_liststore.append([x, False])

    # Реакция на выбор в окне MyPLS
    def my_pls_on_cell_radio_toggled(self, widget, path):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            c = self.my_pls_liststore.get_iter(path)
            for key in self.my_pls_config.sections():
                    if key == self.my_pls_liststore.get_value(c, 0):
                        self.id_chan = ['My', self.my_pls_config[key]['addrstation']]
                        self.real_adress = self.my_pls_config[key]['addrstation']
                        print('----------------------------------------')
                        print(self.my_pls_liststore.get_value(c, 0), self.my_pls_config[key]['addrstation'])
                        print('----------------------------------------')
            for row in self.my_pls_liststore:
                row[1] = (row.path == selected_path)

    # Реакция на выбор в окне RadioRecord
    def record_on_cell_radio_toggled(self, widget, path):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            c = self.record_liststore.get_iter(path)
            # Поиск значения в модели и сопоставление адреса в окне RadioRecord
            for key, val in self.record_dict.items():
                if key == self.record_liststore.get_value(c, 0):
                    self.id_chan = ['RREC', val]
                    self.real_adress = val
                    print('----------------------------------------')
                    print(self.record_liststore.get_value(c, 0))
                    print('----------------------------------------')
            for row in self.record_liststore:
                row[1] = (row.path == selected_path)

    # Создание тултипа для медиа информации о потоке
    def media_tool_hint(self, widget, x, y, keyboard_mode, tooltip):

        def local_convert_time(t):

            if t != 18446744073709551615:
                dt = datetime.datetime.utcfromtimestamp(t/1e9)
                mytime = dt.strftime('%H:%M:%S:%f')[:-4].split('::')
                for x in map(lambda x: '%s' % x, mytime):
                    return x
            else:
                return '99:99:99.999999999'

        def m_i():

            if self.tooltip_now_text != '':
                return True

            media_info = []
            discoverer = GstPbutils.Discoverer()
            info = discoverer.discover_uri(self.media_location)# Create = GstPbutils.DiscovererInfo

            name_command_info = ['формат','разное', 'следующее', 'тип',
            'токен', 'битность', 'каналы', 'глубина', 'язык',
            'максимальная битность', 'частота дискретизации',
            'продолжительность']

            for ainfo in info.get_audio_streams():# Create = GstPbutils.DiscovererStreamInfo

                if self.tooltip_now_text != '':
                    return True

                name_metod_info = [str(ainfo.get_caps()).split(',')[0], str(ainfo.get_misc()), str(ainfo.get_next()),
                str(ainfo.get_stream_type_nick()), str(ainfo.get_toc()), str(ainfo.get_bitrate()),
                str(ainfo.get_channels()), str(ainfo.get_depth()), str(ainfo.get_language()), str(ainfo.get_max_bitrate()),
                str(ainfo.get_sample_rate()), str(local_convert_time(info.get_duration()))]

                for j in range(0, 12):
                    if name_metod_info[j] != 'None' and name_metod_info[j] != '0':
                        media_info.append(str(name_command_info[j])+' = '+str(name_metod_info[j])+'\n')
                    else:
                        pass

            self.tooltip_now_text = ''
            for x in media_info:
                self.tooltip_now_text += x

        if self.pipeline:

            if len(self.tooltip_now_text) > 0:
                pass
            else:
                self.thread_t = threading.Thread(target=m_i, daemon=True)
                self.thread_t.start()

            if self.thread_t.is_alive():
                tooltip.set_text('Идет поиск данных')
                return True
            else:
                tooltip.set_text(self.tooltip_now_text)
                return True
        else:
            tooltip.set_text('Нет информации')
        return True

    # Создание адресного листа для IRC при первом запуске
    def create_irc_list(self, *args):

        # Удаление элементов на основной форме
        self.w_label.destroy()
        self.w_batton1.destroy()
        self.w_batton2.destroy()
        self.w_grid.destroy()

        # Запуск диалога
        dialog = DialogC_A_L(self, args[1])
        response = dialog.run()

        if response == 22:
            # Создание и установка элементов
            self.loc_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
            self.loc_config.read(self.prog_full_path + '/radiointernet.txt', encoding = 'utf-8')
            self.c_s = self.loc_config.sections()
            self.liststore_RIC = Gtk.ListStore(str, bool)
            for x in self.c_s:
                self.liststore_RIC.append([x, False])

            self.top_treeview = Gtk.TreeView(model=self.liststore_RIC)
            self.top_treeview.set_tooltip_column(0)
            self.top_treeview.set_enable_search(True)
            self.top_treeview.set_show_expanders(False)

            self.top_renderer_text = Gtk.CellRendererText()
            self.top_column_text = Gtk.TreeViewColumn("Раздел", self.top_renderer_text, text=0)
            self.top_column_text.set_alignment(0.5)
            self.top_column_text.set_max_width(270)
            self.top_column_text.set_min_width(50)
            self.top_column_text.set_fixed_width(270)
            self.top_column_text.set_resizable(False)
            self.top_column_text.set_expand(False)

            self.top_treeview.append_column(self.top_column_text)

            self.top_renderer_radio = Gtk.CellRendererToggle()
            self.top_renderer_radio.set_radio(True)
            self.top_renderer_radio.connect("toggled", self.on_cell_radio_toggled_RIC)

            self.top_column_radio = Gtk.TreeViewColumn("Выбор", self.top_renderer_radio, active=1)
            self.top_column_radio.set_alignment(0.5)
            self.top_column_radio.set_expand(False)
            self.top_column_radio.set_resizable(False)

            self.top_treeview.append_column(self.top_column_radio)

            self.top_window.destroy()

            self.top_window = Gtk.ScrolledWindow()
            self.top_window.set_min_content_height(150)
            self.top_window.set_min_content_width(340)
            self.top_window.add(self.top_treeview)

            self.grid_for_IRC.attach(self.top_window, 1, 1, 10, 6)

            self.top_treeview.show()
            self.top_window.show()
            self.grid_for_IRC.show()

            dialog.destroy()

    # Реакция на выбор в таблице Internet Radio Com Top
    def on_cell_radio_toggled_RIC(self, widget, path):

        self.RIC_url = ''
        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            source_cell = self.liststore_RIC.get_iter(path)
            self.liststore_sub.clear()
            for x in self.c_s:
                if x == self.liststore_RIC.get_value(source_cell, 0):
                    print('----------------------------------------')
                    print(self.liststore_RIC.get_value(source_cell, 0))
                    print('----------------------------------------')
                    self.RIC_url = x
                    for j in self.loc_config[x]:
                        self.liststore_sub.append([re.sub(r'&', r'&amp;', j), False])
            for row in self.liststore_RIC:
                row[1] = (row.path == selected_path)

    # Реакция на выбор Internet Radio Com Sub
    def on_cell_radio_toggled_s_RIC(self, widget, path):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            source_cell = self.liststore_sub.get_iter(path)
            print('----------------------------------------')
            print(self.liststore_sub.get_value(source_cell, 0))
            print('----------------------------------------')
            for row in self.liststore_sub:
                row[1] = (row.path == selected_path)
            nam_adr_irc = re.sub(r'&amp;', r'&', self.liststore_sub.get_value(source_cell, 0), re.M)
            self.real_adress = self.loc_config[self.RIC_url][nam_adr_irc]
            self.id_chan = ['IRC', nam_adr_irc]

    # Реакция на выбор DIFM
    def di_on_cell_radio_toggled(self, widget, path):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            source_cell = self.di_liststore.get_iter(path)
            for key, val in self.d_fm_dict.items():
                if key == self.di_liststore.get_value(source_cell, 0):
                    print('----------------------------------------')
                    print(self.di_liststore.get_value(source_cell, 0))
                    print('----------------------------------------')
                    self.real_adress = val
                    self.id_chan = ['DI', val]
            for row in self.di_liststore:
                row[1] = (row.path == selected_path)

    # Воспроизвести последнюю станцию
    def on_play_last_st(self, *args):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            last_adr = self.wr_station_name_adr.read_last_station()

            print('1 last_adr = self.wr_station_name_adr.read_last_station()', last_adr)

            if '101.ru'.find(last_adr[0]) and not 'pradio22' in str(last_adr[0]):
                self.id_chan[0] = re.sub(r'(.+?\=)(\d+)$', r'\2', str(last_adr[0]), re.S)
                res = last_adr[0]
                if res != 0:
                    self.play_stat_now(res)
                else:
                    pass

            if 'pradio22'.find(last_adr[0]):
                self.id_chan[0] = re.sub(r'(rtmp\:\/\/wz\d+\.101\.ru\/pradio\d+\/)(\d+)(\?setst\=&uid\=\-\d+\/main)', r'\2', str(last_adr[0]), re.S)
                self.play_stat_now(last_adr[0])

            if 'PS' == last_adr[1]:
                print('Select PS')
                self.id_chan[0] = 'PS'
            elif 'Radio-Record' == last_adr[1]:
                print('Select Radio-Record')
                self.id_chan[0] = 'RREC'
            elif 'RadioTun' == last_adr[1]:
                print('Select RadioTun')
                self.id_chan[0] = 'RTUN'
            elif 'My' == last_adr[1]:
                print('Select My')
                self.id_chan[0] = 'My'
            elif 'Internet Radio COM' == last_adr[1]:
                print('Select Internet Radio COM')
                self.id_chan[0] = 'IRC'
            elif 'D-FM' == last_adr[1]:
                print('Select D-FM')
                self.id_chan[0] = 'DI'
            self.play_stat_now(last_adr)

    # Воспроизвести лучшую станцию
    def on_play_best_st(self, *args):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            best_adr = self.wr_station_name_adr.read_best_station()
            print('best_adr = self.wr_station_name_adr.read_best_station() => ', best_adr)

            if len(best_adr[0]) == 0:
                self.label_title.set_label('Нет записи адреса лучшей станции')
                return

            if '101.ru' in str(best_adr) and not 'pradio22' in str(best_adr):
                self.id_chan[0] = int(re.sub(r'(?:.+?channel\=)(\d+)\D+(?:.*?)', r'\1', str(best_adr), re.M))
                res = self.HURL.hack_url_adres(best_adr[0])
                if res != 0:
                    self.play_stat_now(res)
            elif 'My' in str(best_adr):
                print('OK => My')
                self.id_chan = ['My', best_adr[0]]
                self.play_stat_now(best_adr)
            elif 'Internet Radio COM' in str(best_adr):
                print('OK => Internet Radio COM')
                self.id_chan[0] = 'IRC'
                self.play_stat_now(best_adr)
            elif 'Radio-Record' in str(best_adr):
                print('OK => Radio-Record')
                self.id_chan[0] = 'RREC'
                self.play_stat_now(best_adr)
            elif 'RadioTun' in str(best_adr):
                print('OK => RadioTun')
                self.id_chan[0] = 'RTUN'
                self.play_stat_now(best_adr)
            elif 'D-FM' in str(best_adr):
                print('OK => D-FM')
                self.id_chan[0] = 'IRC'
                self.play_stat_now(best_adr)
            elif 'pradio22' in str(best_adr):
                self.id_chan[0] = re.sub(r'(rtmp\:\/\/wz\d+\.101\.ru\/pradio\d+\/)(\d+)(\?setst\=&uid\=\-\d+\/main)', r'\2', str(best_adr), re.S)
                print('best_adr $$$$$$$$$$$$1 ==>>>> ', best_adr)
                self.play_stat_now(best_adr)
            elif not 'pradio22' in str(best_adr) and not '101.ru' in str(best_adr) or 'http' in str(best_adr) or 'rtmp' in str(best_adr):
                self.id_chan = [0,0]
                print('best_adr $$$$$$$$$$$$2 ==>>>> ', best_adr)
                self.play_stat_now(best_adr)

    # Сохранить лучшую станцию
    def on_write_best_st(self, *args):

        if self.radio_play == 1 or self.radio_rtmp_play == 1:
            if args[1] == 0 and self.real_adress != '':
                print('111 ****************************', self.real_adress, self.id_chan)
                param_send = [self.real_adress,self.id_chan[0]]
                self.wr_station_name_adr.write_best_station(param_send)
            elif args[1] == 1:
                print('222 ****************************')
                self.id_chan[0] = re.sub(r'(.+?\=)(\d+)$', r'\2', str(self.wr_station_name_adr.read_best_station()), re.S)
                if self.id_chan[0] == 0 and self.id_chan[1] == 0:
                    print('333 ****************************')
                    self.on_click_bt5()
                else:
                    print('444 ****************************')
                    res = self.HURL.hack_url_adres(self.wr_station_name_adr.read_best_station())
                    print('res &&&&&&&&&&&>>>> ', type(res), res)
                    if res != 0:
                        self.play_stat_now(res)

    # Диалоговое окно поиска персональных станций
    def search_in_personal_station(self, widget):

        def w_c_l(self, *args):
            dialog.destroy()

        dialog = DialogFindPersonalStation(self)
        dialog.connect('delete-event', w_c_l)
        response = dialog.run()
        if response == Gtk.ResponseType.OK:
            self.real_adress = dialog.return_adres
            print('self.real_adress ==> ', self.real_adress)
            self.id_chan[0] = 'PS'
            self.play_stat_now(self.real_adress)
            dialog.destroy()
        elif response == Gtk.ResponseType.CLOSE:
            dialog.destroy()

    # Обновление адресного листа 101
    # Модальное окно с прогрессбаром в отдельном потоке
    def on_refresh_list(self, widget):

        if self.radio_play == 0 and self.radio_rtmp_play == 0:
            pass
        else:
            return False

        self.liststore_101.clear()

        #
        dialog_101_update = Dialog_Update_101(self)
        response_101_update = dialog_101_update.run()
        #

        if response_101_update == -4 or response_101_update == -7:
            dialog_101_update.thread_3_stop.set()
            #
            loc_final_conf = []
            for x in dialog_101_update.loc_dict_101_ru:
                for d in x:
                    loc_final_conf.append(d+'\n')

            with open(self.prog_full_path + '/adres_list.ini', 'w', encoding='utf-8', errors='ignore') as loc_adr101file:
                loc_adr101file.writelines(loc_final_conf)

            with open(self.prog_full_path + '/adres_list.ini', 'r', encoding='utf-8', errors='ignore') as file_w:
                read_adr = file_w.readlines()

            read_list_adr = []

            for x in read_adr:
                read_list_adr.append(re.findall(r'(.+?)\s+=\s(.+?)\n', x, re.S))

            for x in read_list_adr:
                self.liststore_101.append([str(x[0][0]), False])
            #
            dialog_101_update.destroy()
            print("Dialog update for 101RU finished")

        dialog_101_update.destroy()

    # Создание меню в трее
    def create_main_menu(self, *args):

        print('Создание StatusIcon ' + self.get_time_now())

        def pos(menu, icon):
            return (Gtk.StatusIcon.position_menu(menu, args[0]))

        self.main_menu.popup(None, None, pos, self.tray_icon, 0, Gtk.get_current_event_time())
        self.main_menu.show_all()

    # Определение источник "файл или http" и создание элемента source
    def create_source(self, location):

        if location == 0:
            self.on_click_bt5()
            self.label_title.set_text('Канал не передает звукового потока!')
            #raise IOError(" 1 Источник %s не найден" % location)
            return 0
        if len(location) != 0:
            print('***** location ==> ' + self.get_time_now(), location)

            if str(type(location)) == "<class 'str'>" and len(location) > 2:
                location = [location]

            if not str(location[0]).startswith('http') and not str(location[0]).startswith('rtmp') and not os.path.exists(str(location[0])):
                if location[0] == 0:
                    self.label_title.set_text('Канал не передает звукового потока!')
                    return 0
                    print('2 Источник %s не найден' % location)
                    raise IOError("Источник %s не найден" % location)
                    self.My_ERROR_Mess = 0

            media_for_location = location[0]
            if location[0].endswith('.flv'):
                self.media_location = location[0]
                source = Gst.ElementFactory.make('uridecodebin', 'source')
                self.HURL.used_stream_adress.append(location[0])
                source.set_property('uri', location[0])
                print("************* ==> Источник HTTP *.flv "+self.get_time_now())
                if '101.ru' in location[0]:
                    get_id_chanel = re.sub(r'(.+?\=)(\d+)$', r'\2', self.real_adress, re.M)
                    #
                    find_time_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
                    find_time_opener.addheaders = [
                    ('Host', '101.ru'),
                    ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
                    ]

                    with find_time_opener.open('http://f1.101.ru/api/getplayingtrackinfo.php?station_id='+get_id_chanel+'&typechannel=channel') as http_source:
                        j_date = json.loads(str(http_source.read().decode('utf-8', errors='ignore')))
                        restrat_time = int(j_date['result']['finish_time']) - int(j_date['result']['current_time'])
                        GObject.timeout_add_seconds(restrat_time, self.play_stat_now, get_id_chanel)
            if location[0].startswith('http'):
                self.media_location = location[0]
                source = Gst.ElementFactory.make('souphttpsrc', 'source')
                source.set_property('user-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
                self.HURL.used_stream_adress.append(location[0])
                source.set_property('location', location[0])
                print("************* ==> Источник HTTP "+self.get_time_now())
            elif location[0].startswith('rtmp'):
                self.media_location = location[0]
                source = Gst.ElementFactory.make('rtmpsrc', 'source')
                self.HURL.used_stream_adress.append(location[0])
                source.set_property('location', location[0])
                print("************* ==> Источник RTMP "+self.get_time_now())
            elif not location[0].startswith('http') or not location[0].startswith('rtmp') and not location[0].endswith('.flv'):
                self.media_location = 'file://'+str(location[0])
                source = Gst.ElementFactory.make('filesrc', 'source')
                print('************* ==> Источник файл ' + self.get_time_now())
                self.HURL.used_stream_adress.append(location[0])
                source.set_property('location', location[0])
            if len(location) > 1:
                self.id_chan[0] = location[1]

            self.tooltip_now_text = ''
            return source
        else:
            self.label_title.set_text('Канал не передает звукового потока!')
            raise IOError(" 3 Источник %s не найден" % location)
            return 0

    # Создание объекта Pipeline
    def create_pipeline(self, args):

        ## decodebin имеет динамические pad'ы,
        # которые так же динамически необходимо линковать
        def on_pad_added(decodebin, pad):
            caps = pad.get_current_caps()
            pad.link_full(audioconvert.get_static_pad('sink'), Gst.PadLinkCheck.TEMPLATE_CAPS)

        ## Создаем нужные элементы для плеера
        source = self.create_source(args)
        if source == 0:
            self.pipeline = 0
            return 0
        decodebin = Gst.ElementFactory.make('decodebin', 'decodebin')
        audioconvert = Gst.ElementFactory.make('audioconvert', 'audioconvert')
        equalizer = Gst.ElementFactory.make('equalizer-nbands', 'equalizer-nbands')
        self.volume = Gst.ElementFactory.make('volume', 'volume')
        level = Gst.ElementFactory.make('level', 'level')
        queue = Gst.ElementFactory.make('queue2', 'myqueue')
        audiosink = Gst.ElementFactory.make('autoaudiosink', 'autoaudiosink')

        decodebin.connect('pad-added', on_pad_added)
        queue.set_property('use-buffering', True)

        if str(type(self.eq_set_preset)) != "<class 'list'>" and 'Редактировать положение эквалайзера' != str(self.eq_set_preset):
            equalizer.set_property('num-bands', 18)
            chek= 0
            try:
                for x in self.equalizer_presets_dict.get(self.eq_set_preset):
                    band = equalizer.get_child_by_index(chek)
                    band.set_property('freq', self.freq[chek])
                    band.set_property('bandwidth', self.bandwidth[chek])
                    band.set_property('gain', float(x))
                    chek += 1
            except TypeError:
                print('self.eq_set_preset ==> ', self.eq_set_preset, ' ', self.get_time_now())
                for x in self.eq_set_preset:
                    band = equalizer.get_child_by_index(chek)
                    band.set_property('freq', self.freq[chek])
                    band.set_property('bandwidth', self.bandwidth[chek])
                    band.set_property('gain', float(x))
                    chek += 1
        elif str(type(self.eq_set_preset)) == "<class 'list'>":
            equalizer.set_property('num-bands', 18)
            try:
                chek= 0
                for x in self.eq_set_preset:
                    band = equalizer.get_child_by_index(chek)
                    band.set_property('freq', self.freq[chek])
                    band.set_property('bandwidth', self.bandwidth[chek])
                    band.set_property('gain', float(x))
                    chek += 1
            except:# Если отсутствует значение
                no_config = configparser.ConfigParser()
                no_config.read(self.prog_full_path + '/set-eq.ini', encoding='utf-8')
                no_config.set('EQ-Settings','lasteq','0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0')
                leq = config['EQ-Settings']['lasteq'].split(' ')
                self.eq_set_preset = []
                for x in leq:
                    self.eq_set_preset.append(x)
                with open(self.prog_full_path + '/set-eq.ini', 'w') as cfgfile:
                    no_config.write(cfgfile)
                chek= 0
                for x in self.eq_set_preset:
                    band = equalizer.get_child_by_index(chek)
                    band.set_property('freq', self.freq[chek])
                    band.set_property('bandwidth', self.bandwidth[chek])
                    band.set_property('gain', float(x))
                    chek += 1

        self.pipeline = Gst.Pipeline()

        print('Создан self.pipeline ' + self.get_time_now())

        if [self.pipeline.add(k) for k in [source, decodebin, audioconvert, equalizer, self.volume, level, queue, audiosink]]:
            print('OK Pipeline Add Elements ' + self.get_time_now())

        ## линкуем элементы между собой
        if source.link(decodebin):
            print('1 source.link(decodebin) ==> OK LINKED')
        if audioconvert.link(queue):
            print('2 audioconvert.link(queue) ==> OK LINKED')
        if queue.link(level):
            print('3 queue.link(level) ==> OK LINKED')
        if level.link(self.volume):
            print('4 level.link(self.volume) ==> OK LINKED')
        if self.volume.link(equalizer):
            print('5 self.volume.link(equalizer) ==> OK LINKED')
        if equalizer.link(audiosink):
            print('6 equalizer.link(audiosink) ==> OK LINKED')

        if self.run_radio_window == 0 and self.real_vol_save == 0:
            self.real_vol_save = 0.50
            self.scal_sl.set_value(0.50)
            self.volume.set_property('volume', 0.50)
        else:
            self.scal_sl.set_value(self.real_vol_save)
            self.volume.set_property('volume', self.real_vol_save)

        ## получаем шину и вешаем на нее обработчики
        message_bus = self.pipeline.get_bus()
        message_bus.add_signal_watch_full(1)
        message_bus.connect('message::eos', self.message_eos)
        message_bus.connect('message::tag', self.message_tag)
        message_bus.connect('message::error', self.message_error)
        message_bus.connect('message::element', self.message_element)
        message_bus.connect('message::duration', self.message_duration)
        message_bus.connect('message::buffering', self.message_buffering)

        self.pipeline.set_state(Gst.State.PAUSED)

        self.run_radio_window = 1

    # Конвертация полученых наносекунд в часы минуты секунды милисекунды
    def convert_time(self, t):

        end_res = ''
        mytime = datetime.datetime.utcfromtimestamp(t/1e9).strftime('%H:%M:%S:%f')[:-4].split('::')
        for x in map(lambda x: '%s' % x, mytime):
            end_res = x
        return end_res

    # Установка времени/продолжительности звучания
    def set_time_from_stream(self, *user_date):

        if (self.radio_play or self.file_play or self.radio_rtmp_play) and self.pipeline != 0:

            play_position = self.pipeline.query_position(Gst.Format.TIME)[1]
            total_length = self.pipeline.query_duration(Gst.Format.TIME)[1]

            if play_position != 0 and total_length != 0 and self.pipeline.query_duration(Gst.Format.TIME)[0] == True:

                if total_length != -1 and play_position < total_length:

                    self.label_time.set_label(self.convert_time(play_position))
                    self.label_ltime.set_label(self.convert_time(total_length-play_position))

                elif total_length == -1:

                    self.label_time.set_label(self.convert_time(play_position))
                    self.label_ltime.set_label('00:00:00:00')

            return True

        else:

            if self.timer_time:

                GObject.source_remove(self.timer_time)

            return False

    # Получение названия
    def get_title_from_url(self, adres):

        try:

            print('adres[0] = ', adres[0])

        except ValueError:

            if self.timer_title:
                GObject.source_remove(self.timer_title)
                return False

        id_chan_req  = adres[0]
        title_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        title_opener.addheaders = [
        ('Host', '101.ru'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

        try:
            with title_opener.open('http://101.ru/?an=channel_playlist&channel='+str(id_chan_req)) as source_title_http:
                razdel_title_http = source_title_http.read().decode('utf-8', errors='ignore')
            find_title_in_url_stream = re.findall(r'class\="icon.+?>(\w.+?)<', razdel_title_http, re.M)
        except HTTPError as e:
            print('The server couldn\'t fulfill the request.', e.code)
        except URLError as e:
            print('We failed to reach a server.', e.code)
        try:
            print('get_title_from_url(self, adres) ==> ', find_title_in_url_stream[0], '$<==#==>$', self.label_title.get_text())
            print('Устанавливается значение title из get_title_from_url')
            print('self.label_title.get_text()', self.label_title.get_text())
            print('find_title_in_url_stream[0]', find_title_in_url_stream[0])
            if not self.label_title.get_text().find(find_title_in_url_stream[0]):
                a = self.label_title.get_text()
                self.label_title.set_label(str(a)+' - '+str(find_title_in_url_stream[0]))
                if self.timer_title:
                    GObject.source_remove(self.timer_title)
        except IndexError:
            if str(self.label_title.get_text()) == '':
                self.label_title.set_label('')
                if self.timer_title:
                    GObject.source_remove(self.timer_title)

    # Установка нового места начала востпроизведения
    def new_seek_pos_set(self, widget, pos):

        try:
            if pos.button == 3:
                return False
        except AttributeError:
            pass

        if 'MenuItem' in str(widget):

            self.pipeline.set_state(Gst.State.PAUSED)

            self.pipeline.seek_simple(
            Gst.Format.TIME,
            Gst.SeekFlags.FLUSH | Gst.SeekFlags.ACCURATE, int(pos * Gst.SECOND))

            self.pipeline.set_state(Gst.State.PLAYING)
            print('SEEK => if self.pipeline:')

        if 'HScale' in str(widget):
            a = self.seek_line.get_value()
            self.pipeline.set_state(Gst.State.PAUSED)

            self.pipeline.seek_simple(
            Gst.Format.TIME,
            Gst.SeekFlags.FLUSH | Gst.SeekFlags.ACCURATE,
            int(a * (int(self.pipeline.query_duration(Gst.Format.TIME)[1])/100)))

            self.pipeline.set_state(Gst.State.PLAYING)
            print('SEEK => if self.pipeline:')

    # Продвижение ползунка по мере звучания файла
    def update_seek_line(self, *user_date):

        try:
            try:
                play_position = self.pipeline.query_position(Gst.Format.TIME)[1]
                total_length = self.pipeline.query_duration(Gst.Format.TIME)[1]
                self.seek_line.set_value(round((play_position/1000000000)/((total_length/1000000000)/100), 2))
                return True
            except AttributeError:
                play_position = 0
                total_length = 0
                if self.timer:
                    GObject.source_remove(self.timer)
        except ZeroDivisionError:
            return True

    # Создание Pop-Up Menu для CUE файлов на полосе воспроизведения
    def popup_for_cue_on_seek_line(self, widget, event):

        if self.cue_file_find == 0:
            return False

        cue_file_name = [x for x in os.listdir(self.cue_file_find[1]) if x == str(self.cue_file_find[0] + '.cue')]

        if event.button == 3:

            if len(cue_file_name) > 0:

                with open(str(self.cue_file_find[1]) +'/'+ str(cue_file_name[0]), 'r', encoding='cp1251', errors='ignore') as cue_f:
                    source_cue = cue_f.read()

                rez = re.findall(r'TRACK (\d+) AUDIO.+?TITLE (.+?)\n.+?PERFORMER (.+?)\s.+?INDEX 01 (.+?)\s', source_cue, re.S)

                pop_menu = []
                time_for_menu = []

                self.menu_pop_show = Gtk.Menu()

                for x in [x for x in rez]:
                    a = x[1].split(':')
                    t = x[3].split(':')
                    pop_menu.append(Gtk.MenuItem(re.sub(r'"', r' ', a[0])))
                    time_for_menu.append((int(t[0]) * 60) + int(t[1]))

                check_t = 0
                for x in pop_menu:
                    x.connect('activate', self.new_seek_pos_set, time_for_menu[check_t])
                    self.menu_pop_show.append(x)
                    check_t += 1

                self.menu_pop_show.show_all()
                self.menu_pop_show.popup(None, None, None, None, event.button, event.get_time())

    #꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾#
    ################### ######### #####################
    #################### ####### ######################
    ##################### ##### #######################
    ###################### ### ########################
    ####################### # #########################
    ######################## ##########################

    # Обработка сообщений от элементов
    def message_element(self, bus, message):

        def mess_rms_set(m):

            if m.type == Gst.MessageType.ELEMENT:

                s = Gst.Message.get_structure(m)
                if s.get_name() != 'level':
                    return False
                else:
                    try:
                        v_rms_0 = int(s.get_value('rms')[0])
                        v_rms_1 = int(s.get_value('rms')[1])
                    except:
                        v_rms_0 = int(s.get_value('rms')[0])
                        v_rms_1 = int(s.get_value('rms')[0])
                    if (v_rms_0 < -80 or v_rms_1 < -80) and self.radio_play:
                        self.s_rms_chek.append(v_rms_0)
                        self.s_rms_chek.append(v_rms_1)
                    if sum(self.s_rms_chek) < -2000:
                        print('if sum(self.s_rms_chek) < -2000: ==> self.pipeline.set_state(Gst.State.NULL)')
                        self.pipeline.set_state(Gst.State.NULL)
                        self.s_rms_chek = [0]
                        self.pipeline = 0
                        self.play_stat_now()
                    try:
                        if self.HURL.check_stream_adress == 0 and '101.ru' in self.id_chan[0]:
                            self.s_rms_chek = [0]
                    except:
                        pass
                    else:

                        if self.HURL.check_stream_adress != 0:
                            self.HURL.check_stream_adress = 0

                        rms0 = abs(v_rms_0)
                        rmsdb = 10 * math.log(rms0 / 32768 )
                        vlrms = (rmsdb-self.min_dcb) * 100 / (self.max_dcb-self.min_dcb)

                        rms1 = abs(v_rms_1)
                        rmsdb1 = 10 * math.log(rms1 / 32768 )
                        vlrms1 = (rmsdb1-self.min_dcb) * 100 / (self.max_dcb-self.min_dcb)

                        GLib.idle_add(self.level_bar_l.set_fraction, abs(round(vlrms/100, 2)))
                        GLib.idle_add(self.level_bar_r.set_fraction, abs(round(vlrms1/100, 2)))

        #if Gst.Structure.get_name(Gst.Message.get_structure(message)) == 'level':
        thread_rms = threading.Thread(target=mess_rms_set(message), daemon=True)
        thread_rms.start()

    # Обработка сообщений продолжительности
    def message_duration(self, bus, message):

        if message.type == Gst.MessageType.DURATION_CHANGED:
            print('message.type == Gst.MessageType.DURATION_CHANGED')
            s = Gst.Message.get_structure(message)
            if self.radio_play:
                self.timer_title = GObject.timeout_add(1000, self.get_title_from_url, self.id_chan[0])

    # Обработка сообщений ошибок
    def message_error(self, bus, message):

        if message.type == Gst.MessageType.ERROR:
            self.My_ERROR_Mess = True
            mpe = message.parse_error()
            print('Получено ERROR сообщение с ошибкой ' + self.get_time_now(), '\n', type(mpe), '\n', mpe)
            if 'Redirect to: (NULL)' in str(mpe):
                print('if Redirect to: (NULL) in str(mpe): ==> self.pipeline.set_state(Gst.State.NULL) ' + self.get_time_now())
                #
                #
                try:
                    #
                    test_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
                    test_opener.addheaders = [
                    ('Host', 'www.google.ru'),
                    ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

                    with test_opener.open('http://www.google.ru/') as test_req_http:
                        self.pipeline.set_state(Gst.State.NULL)
                        self.pipeline = 0
                        self.play_stat_now()
                except HTTPError as e:
                    self.pipeline.set_state(Gst.State.NULL)
                    self.pipeline = 0
                    self.on_click_bt5()
                    self.label_title.set_text('Отсутствует интернет соединение')
                    self.My_ERROR_Mess = 0
                except URLError as e:
                    self.pipeline.set_state(Gst.State.NULL)
                    self.pipeline = 0
                    self.on_click_bt5()
                    self.label_title.set_text('Отсутствует интернет соединение')
                    self.My_ERROR_Mess = 0
                #
                #
            if 'Could not detect type of contents' in str(mpe) or 'No such file' in str(mpe):
                self.label_title.set_text('Ошибка чтения потока...')
                #
                if self.file_play == 1:
                    print('В виду ошибки чтения данных получено сообщение об окончании потока ' + self.get_time_now())
                    self.level_bar_l.set_fraction(1.0)
                    self.level_bar_r.set_fraction(1.0)
                    self.label_time.set_label('00:00:00:00')
                    self.label_ltime.set_label('00:00:00:00')
                    self.seek_line.set_value(float(0.01))
                    self.pipeline.set_state(Gst.State.NULL)

                    Gst.Event.new_flush_stop(True)

                    if len(self.f_name_len) >= 2:
                        self.f_name_len.pop(0)
                        self.pipeline.set_state(Gst.State.NULL)
                        self.pipeline = 0
                        try:
                            self.create_pipeline(self.f_name_len[0])
                            self.pipeline.set_state(Gst.State.PLAYING)
                        except:
                            self.pipeline.set_state(Gst.State.NULL)
                    else:
                        self.on_click_bt5()
                elif self.radio_play == 1:
                    self.pipeline.set_state(Gst.State.NULL)
                    self.pipeline = 0
                    self.play_stat_now()

    # Обработка сообщений содержащих ТЭГИ
    def message_tag(self, bus, message):

        if message.type == Gst.MessageType.TAG:
            tag_l = message.parse_tag()

            s_tag_l = []
            for h in self.get_info_tag:
                if tag_l.get_string(h)[0] == True:
                    if h == 'organization':
                        self.tag_organization = tag_l.get_string(h)[1]
                    if '101.ru' in str(tag_l.get_string(h)):
                        s_tag_l.append(re.sub(r'(101\.ru\:\s?)(.+?)$', r'\2 ', str(tag_l.get_string(h)[1]), re.M))
                    else:
                        s_tag_l.append(re.sub(r'/', r' ', tag_l.get_string(h)[1]))
                else:
                    pass

            if len(s_tag_l) > 0:
                try:
                    self.label_title.set_label(re.sub(r' \- 0\:00', r'', str(self.lang_ident_str(' - '.join(s_tag_l))), re.M))
                except:
                    pass

            if self.file_play == 0 and not self.timer_title and self.id_chan[0][0].isdigit():
                self.timer_title = GObject.timeout_add(1000, self.get_title_from_url, self.id_chan[0])

    # Обработка сообщений конца потока
    def message_eos(self, bus, message):

        if message.type == Gst.MessageType.EOS:
            print('Получено сообщение об окончании потока ' + self.get_time_now())
            if self.file_play == 1:
                print(' \n end of track \n')
                self.level_bar_l.set_fraction(1.0)
                self.level_bar_r.set_fraction(1.0)
                self.label_time.set_label('00:00:00:00')
                self.label_ltime.set_label('00:00:00:00')
                self.seek_line.set_value(float(0.01))
                print('eos1 self.pipeline.set_state(Gst.State.NULL)')
                self.pipeline.set_state(Gst.State.NULL)

                Gst.Event.new_flush_stop(True)

                if len(self.f_name_len) >= 2:
                    #
                    for x in range(len(self.playlist_liststore)):
                        self.playlist_liststore.set_value(self.playlist_liststore.get_iter(x), 0, None)

                    for x in range(len(self.playlist_liststore)):

                        d_check = x + 1
                        try:
                            g_iter = self.playlist_liststore.get_iter(d_check)
                        except:
                            g_iter = self.playlist_liststore.get_iter(x)

                        if str(os.path.basename(self.f_name_len[0])) == str(self.playlist_liststore.get_value(self.playlist_liststore.get_iter(x), 1)):
                            self.playlist_liststore.set_value(self.playlist_liststore.get_iter(x), 0, None)
                            self.playlist_liststore.set_value(g_iter, 0, Gtk.STOCK_MEDIA_PLAY)
                    #
                    print('len(self.f_name_len) ==> ', len(self.f_name_len))
                    self.f_name_len.pop(0)
                    print('eos2 self.pipeline.set_state(Gst.State.NULL)')
                    self.pipeline.set_state(Gst.State.NULL)
                    self.pipeline = 0
                    try:
                        self.create_pipeline(self.f_name_len[0])
                        self.pipeline.set_state(Gst.State.PLAYING)
                    except:
                        print('except: ++> self.pipeline.set_state(Gst.State.NULL)')
                        self.pipeline.set_state(Gst.State.NULL)
                else:
                    print('************** self.on_click_bt5()')
                    self.on_click_bt5()
            elif self.radio_play == 1:
                print('Gst.MessageType.EOS self.My_ERROR_Mess = ' + self.get_time_now(), self.My_ERROR_Mess)
                self.pipeline.set_state(Gst.State.NULL)
                self.pipeline = 0
                self.play_stat_now()

    # Buffering
    def message_buffering(self, bus, message):

        if message.type == Gst.MessageType.BUFFERING:
            if message.parse_buffering() == 100:
                print('Buffering is done = ', message.parse_buffering())
                self.pipeline.set_state(Gst.State.PLAYING)

        ####################### ###########################
        ###################### # ##########################
        ##################### ### #########################
        #################### ##### ########################
        ################### ####### #######################
        ################## ######### ######################
        #꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾꙾#

    # Действие для передачи пользовательского адреса из диалога
    '''
    Нет проверки на 101.ru
    '''
    def on_dialog_choice(self, widget):

        if self.file_play == 0 and self.radio_play == 0 and self.radio_rtmp_play == 0:
            dialog = DialogEntryAdr(self)
            response = dialog.run()

            if response == Gtk.ResponseType.OK:
                self.real_adress = dialog.entry.get_text()
                print("The OK button was clicked", self.real_adress)
                self.id_chan = ['My', self.real_adress]
                self.play_stat_now(self.real_adress)
            elif response == Gtk.ResponseType.CANCEL:
                print("The Cancel button was clicked")
                dialog.destroy()

            dialog.destroy()

    # Реакция на нажатие радиобаттон в модели 101
    def on_cell_radio_toggled(self, widget, path):

        if self.radio_play == 0 and self.radio_rtmp_play == 0:
            selected_path = Gtk.TreePath(path)
            c = self.liststore_101.get_iter(path)
            # Поиск значения в модели и сопоставление с адресом
            for x in self.read_list_adr:
                if str(x[0][0]) == str(self.liststore_101.get_value(c, 0)):
                    self.id_chan[0] = re.findall(r'.+?(\d+)$', x[0][1])
                    self.real_adress = re.sub(r'amp;', r'', 'http://101.ru'+x[0][1])
                    print('----------------------------------------')
                    print(self.liststore_101.get_value(c, 0))
                    print('----------------------------------------')
            # Установка точки в радиобаттон
            for row in self.liststore_101:
                row[1] = (row.path == selected_path)

    # Функция воспроизведения
    def play_stat_now(self, f_name=''):

        if self.pipeline != 0:
            return False

        # Если пусто то http
        print('self.id_chan => ', self.id_chan, type(self.id_chan[0]))
        if (self.id_chan[0] == 'RREC' \
        or self.id_chan[0] == 'RTUN' \
        or self.id_chan[0] == 'DI' \
        or self.id_chan[0] == 'IRC' \
        or self.id_chan[0] == 'My' \
        or self.id_chan[0] == 'PS') and not '101.ru' in str(self.id_chan[1]):

            for x in range(6):
                if x == 5:
                    self.button_array[x].show()

            print("if 'http' in str(f_name) or 'rtmp' in str(f_name):  ",
            f_name, 'self.real_adress ==> 1 ',
            self.real_adress)
            thread_1 = threading.Thread(
            target=self.wr_station_name_adr.write_last_station(
            self.real_adress, self.id_chan),
            daemon=True)
            thread_1.start()

            self.file_play = 0
            self.radio_play = 1
            print('Включение радио 1 ' + self.get_time_now())
            if f_name:
                self.uri = f_name
            else:
                self.uri = self.id_chan[1]
            if not self.pipeline:
                for x in range(3):
                    self.button_array[x].hide()
                self.seek_line.hide()#SeekLine
                self.playlist_scrolled_window.hide()
                self.label_title.set_label('')
                self.create_pipeline(self.uri)
                if self.pipeline != 0:
                    self.timer_time = GObject.timeout_add(250, self.set_time_from_stream, None)
                if 'rtmp' in str(f_name):
                    self.file_play = 0
                    self.radio_play = 0
                    self.radio_rtmp_play = 1
                    print('f_name', f_name)
                    self.get_title_song_personal_station(re.sub(r'(rtmp:\/\/wz7\.101\.ru\/pradio22\/)(.+?)(\?setst\=\&uid\=\-1\/main)', r'\2', f_name))
                elif not 'rtmp' in str(f_name):
                    self.radio_rtmp_play = 0
            else:
                self.on_click_bt5()
                self.label_title.set_label('Нет рабочих потоков')
            if self.My_ERROR_Mess:
                print('if self.My_ERROR_Mess: ==> self.pipeline.set_state(Gst.State.NULL)')
                self.pipeline.set_state(Gst.State.NULL)
                self.on_click_bt5()
                self.label_title.set_text('Отсутствует поток')
                self.My_ERROR_Mess = 0
            else:
                self.My_ERROR_Mess = False
                return True
        elif '101.ru' in self.id_chan[0] or (f_name == '' and f_name != 0 and not 'http' in str(f_name) and not 'rtmp' in str(f_name)):

            for x in range(6):
                if x == 5:
                    self.button_array[x].show()

            self.file_play = 0
            self.radio_play = 1
            print('Включение радио 2 ' + self.get_time_now())
            if self.real_adress:
                self.uri = self.HURL.hack_url_adres(re.sub(r'&amp;', r'&', self.real_adress))
            else:
                self.uri = self.HURL.hack_url_adres(re.sub(r'&amp;', r'&', f_name))
            if not self.pipeline and self.uri != 0:
                for x in range(3):
                    self.button_array[x].hide()
                self.seek_line.hide()#SeekLine
                self.playlist_scrolled_window.hide()
                self.label_title.set_label('')
                self.create_pipeline(self.uri)
                if self.pipeline != 0:
                    self.timer_time = GObject.timeout_add(250, self.set_time_from_stream, None)
                    print('self.real_adress ==> 2 ', self.real_adress)
                    thread_2 = threading.Thread(
                    target=self.wr_station_name_adr.write_last_station(
                    self.real_adress, self.id_chan),
                    daemon=True)
                    thread_2.start()
            else:
                self.on_click_bt5()
                self.label_title.set_label('Нет рабочих потоков')
        elif self.id_chan[0] == 'file':# Если не пусто то файл

            for x in range(6):
                if x == 5:
                    self.button_array[x].show()

            self.radio_play = 0
            self.file_play = 1

            print('Включение проигрывания файла ' + self.get_time_now())

            #self.f_name_len = []

            for x in range(3):
                self.button_array[x].hide()

            if 'list' in str(type(f_name)):
                self.playlist_scrolled_window.show()
                #for x in f_name:
                #for k, v in self.playlist_dict.items():
                    #self.f_name_len.append(k)
                self.create_pipeline(self.f_name_len[0])
                self.timer = GObject.timeout_add(500, self.update_seek_line, None)
                self.timer_time = GObject.timeout_add(250, self.set_time_from_stream, None)
            else:
                self.playlist_scrolled_window.show()
                self.create_pipeline(f_name)
                self.timer = GObject.timeout_add(500, self.update_seek_line, None)
                self.timer_time = GObject.timeout_add(250, self.set_time_from_stream, None)

            self.seek_line.show()

        elif f_name == 0:
            print('Нет потока для воспроизведения')
            return False

    # Кнопка плей
    def on_click_bt1(self, b1):

        print('Нажата кнопка Play')

        try:
            if sum(self.id_chan) == 0:
                return False
        except TypeError:

            for x in self.id_name_station:
                if x in self.id_chan[0]:
                    self.main_note_for_cont.set_show_tabs(False)
                    self.play_stat_now(self.real_adress)

            if self.id_chan[0] != 0:
                self.main_note_for_cont.set_show_tabs(False)
                self.play_stat_now()

    # Кнопка открыть файл
    def on_click_bt2(self, b2):

        print('Нажата кнопка File')
        dialog = Gtk.FileChooserDialog(title="Select a File", action=Gtk.FileChooserAction.OPEN,
        buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK))

        ffilter = Gtk.FileFilter()

        file_pattern = ['*.aac', '*.ape', '*.flac', '*.mp3', '*.m4a',
        '*.m4p', '*.ogg', '*.oga', '*.raw', '*.wav',]

        ffilter.set_name("Audio files")
        for x in file_pattern:
            ffilter.add_pattern(x)

        dialog.add_filter(ffilter)

        response = dialog.run()

        if response == Gtk.ResponseType.OK:
            filename = dialog.get_filename()
            self.cue_file_find = [re.sub(r'(.+\/)(.+?)\.\w+$', r'\2', filename), dialog.get_current_folder()]
            self.id_chan[0] = 'file'
            # Notebook HIDE
            self.main_note_for_cont.hide()
            # PlayList SHOW
            self.playlist_scrolled_window.show()
            self.file_play = 1

            self.playlist_liststore.clear()
            self.playlist_dict = {}
            self.playlist_dict = {os.path.basename(filename): filename}
            self.playlist_file = filename

            self.playlist_liststore.append([None, os.path.basename(filename)])

        elif response == Gtk.ResponseType.CANCEL:
            dialog.destroy()
        dialog.destroy()

    # Кнопка открыть папку
    def on_click_bt3(self, b3):

        print('Нажата кнопка Dir')
        filename = []
        dialog = Gtk.FileChooserDialog(title="Select a Folder", action=Gtk.FileChooserAction.SELECT_FOLDER,
        buttons=(Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL, Gtk.STOCK_OPEN, Gtk.ResponseType.OK))

        ffilter = [".ape", ".aac", ".flac", ".mpc", ".mp3", ".m4a",
         ".m4p", ".ogg", ".oga", ".raw", ".wav"]

        dialog.set_select_multiple(True)
        dialog.set_current_folder_uri("file://"+os.getcwd())
        response = dialog.run()

        if response == Gtk.ResponseType.OK:
            dirname = dialog.get_filenames()
            all_file_name = sorted(os.listdir(dirname[0]))
            for x in all_file_name:
                for z in ffilter:
                    if z in dirname[0]+'/'+x:
                        filename.append(dirname[0]+'/'+x)
            self.id_chan[0] = 'file'

            self.playlist_liststore.clear()
            self.playlist_dict = {os.path.basename(a): a for a in filename}
            self.playlist_file = [a for a in filename]

            for x in filename:
                self.playlist_liststore.append([None, os.path.basename(x)])

            try:
                if os.path.isfile(re.sub(r'(.+?)(\.\w+)$', r'\1', filename[0]) + '.cue'):
                    self.cue_file_find = [re.sub(r'(.+?)(\.\w+)$', r'\1', os.path.basename(filename[0])), dialog.get_current_folder()]
                else:
                    self.cue_file_find = 0
            except:
                self.cue_file_find = 0

            # Notebook HIDE
            self.main_note_for_cont.hide()
            # PlayList SHOW
            self.playlist_scrolled_window.show()
            self.file_play = 1

        elif response == Gtk.ResponseType.CANCEL:
            dialog.destroy()
        dialog.destroy()

    # Кнопка пауза
    def on_click_bt4(self, *b4):

        print('Нажата кнопка Pause')
        if self.pipeline:
            if '<enum GST_STATE_PLAYING of type GstState>' in str(self.pipeline.get_state(Gst.CLOCK_TIME_NONE)[1]):
                self.pipeline.set_state(Gst.State.PAUSED)
                return True
            elif '<enum GST_STATE_PAUSED of type GstState>' in str(self.pipeline.get_state(Gst.CLOCK_TIME_NONE)[1]):
                self.pipeline.set_state(Gst.State.PLAYING)
                return True

    # Кнопка стоп
    def on_click_bt5(self, *b5):

        print('Нажата кнопка Stop')

        if self.file_play == 1:
            # Notebook HIDE
            self.main_note_for_cont.show()
            # PlayList SHOW
            self.playlist_scrolled_window.show()

        for x in range(len(self.playlist_liststore)):
            self.playlist_liststore.set_value(self.playlist_liststore.get_iter(x), 0, None)

        for x in range(6):
            if x == 5:
                self.button_array[x].hide()
            else:
                self.button_array[x].show()

        # Снять чекбоксы с плейлистов DI-FM
        for x in self.di_liststore:
            x[1] = False
        # Снять чекбоксы с плейлистов 101
        for x in self.liststore_101:
            x[1] = False
        # Снять чекбоксы с плейлистов RIC
        try:
            for x in self.liststore_RIC:
                x[1] = False
        except AttributeError:
            pass
        for x in self.liststore_sub:
            x[1] = False
        # Снять чекбоксы с плейлистов Record
        for x in self.record_liststore:
            x[1] = False
        # Снять чекбоксы с плейлистов MyPlaylist
        for x in self.my_pls_liststore:
            x[1] = False
        #!!!!!!!!!!!

        # STOP RECORDING
        if self.rec_obj:
            self.rec_status = False
            self.rec_obj.rec_pipeline.set_state(Gst.State.NULL)
            self.rec_obj = 0

        self.tooltip_now_text = ''
        self.id_chan = [0,0]
        self.real_adress = ''
        self.tag_organization = ''
        self.radio_play = 0
        self.radio_rtmp_play = 0
        self.file_play = 0
        self.timer_title = 0
        self.timer = 0
        self.cue_file_find = 0

        if self.timer_rtun_title:
            self.timer_rtun_title = 0

        if self.timer_title_rtmp:
            self.timer_title_rtmp = 0

        self.seek_line.hide()#SeekLine
        self.seek_line.set_value(0.01)
        self.label_title.set_label('')

        if self.pipeline:
            self.main_note_for_cont.set_show_tabs(True)
            self.main_note_for_cont.set_show_border(True)
            print('if self.pipeline: $$$ ==> self.pipeline.set_state(Gst.State.NULL) ' + self.get_time_now())
            self.pipeline.set_state(Gst.State.NULL)

        self.pipeline = 0
        self.level_bar_l.set_fraction(0.0)
        self.level_bar_r.set_fraction(0.0)
        self.label_time.set_label('00:00:00:00')
        self.label_ltime.set_label('00:00:00:00')

    # Кнопка записи
    def on_click_bt6(self, *b6):

        if not self.rec_status:

            print('Recording start', self.HURL.used_stream_adress[-1])

            self.rec_obj = RecorderBin(self.HURL.used_stream_adress[-1])
            self.rec_obj.rec_pipeline.set_state(Gst.State.PLAYING)
            self.rec_status = 1

    # Обработка выбора пункта в меню Equalizer
    def change_equlaizer(self, *gain):

        if (self.radio_rtmp_play == 1 or self.radio_play == 1 or self.file_play == 1) and str(gain[1]) != 'Редактировать положение эквалайзера':
            print('def change_equlaizer(self, *gain):', str(gain[1]))
            eq_config = configparser.ConfigParser()
            eq_config.read(self.prog_full_path + '/set-eq.ini', encoding='utf-8')
            eq_set = []
            self.eq_set_preset = gain[1]
            eq = self.pipeline.get_by_name('equalizer-nbands')
            try:
                chek= 0
                for x in self.equalizer_presets_dict.get(gain[1]):
                    band = eq.get_child_by_index(chek)
                    band.set_property('freq', self.freq[chek])
                    band.set_property('bandwidth', self.bandwidth[chek])
                    band.set_property('gain', x)
                    eq_set.append(int(x))
                    chek += 1
            except:
                pass

            eq_config.set('EQ-Settings','lasteq',''.join(str(eq_set)).strip('][').replace(',', ''))
            with open(self.prog_full_path + '/set-eq.ini', 'w') as cfgfile:
                eq_config.write(cfgfile)

    # Функция установки громкости
    def on_valu_ch(self, obj_send, value, *args):

        if 'VolumeButton' in str(obj_send):
            for x in self.vol_menu:
                if int(x.get_label()) == round(int(self.scal_sl.get_value() * 100)/5)*5:
                    x.set_active(True)

        r_value = round(Decimal.from_float(value), 2)

        if 'CheckMenuItem' in str(obj_send):
            self.scal_sl.set_value(r_value)

        if self.pipeline != 0 and r_value != self.real_vol_save:

            self.scal_sl.set_value(r_value)
            self.volume.set_property('volume', r_value)

        self.real_vol_save = r_value

    # Диалог редактирования пользовательских пресетов эквалайзера
    def edit_eq(self, widget):

        if self.radio_play == 1 or self.radio_rtmp_play == 1 or self.file_play == 1:
            dialog = EQWindow(self)
            response = dialog.run()

            if response == Gtk.ResponseType.OK:
                m_edit_eq = dialog.mdict

                print('m_edit_eq ==> ', m_edit_eq)
                self.eq_set_preset = [int(x) for x in m_edit_eq]
                eq = self.pipeline.get_by_name('equalizer-nbands')
                chek= 0
                for x in self.eq_set_preset:
                    band = eq.get_child_by_index(chek)
                    band.set_property('freq', self.freq[chek])
                    band.set_property('bandwidth', self.bandwidth[chek])
                    band.set_property('gain', float(x))
                    chek += 1
            elif response == Gtk.ResponseType.CANCEL:
                print("The Cancel button was clicked")

            dialog.destroy()

    # Получение названия трека персональных станций
    def get_title_song_personal_station(self, idch):

        if self.radio_rtmp_play == 1:
            id_ch = idch
            print('id_ch ==> ', id_ch)

            person_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
            person_opener.addheaders = [
            ('Host', '101.ru'),
            ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

            chek = 0
            while chek < 3:
                try:
                    # Запрос
                    with person_opener.open('http://f1.101.ru/api/getplayingtrackinfo.php?station_id='+id_ch+'&typechannel=personal') as source_person:
                        html = source_person.read().decode('utf-8', errors='ignore')
                    find_pars = json.loads(html)

                    find_title_song_from_stream = find_pars['result']['title']
                    find_start_song_stream = int(find_pars['result']['start_time'])
                    find_stop_song_stream = int(find_pars['result']['finish_time'])
                    find_query_song_stream = int(find_pars['result']['query_time'])
                    find_current_song_stream = int(find_pars['result']['current_time'])
                    find_duration_song_stream = int(find_pars['result']['duration_sec'])

                    self.label_title.set_label(re.sub(r'&amp;|&#\d+;', r'',find_title_song_from_stream))

                    if find_duration_song_stream > 0 and find_start_song_stream == find_stop_song_stream:
                        print('1', find_duration_song_stream)
                        t_time_s = find_duration_song_stream - (find_query_song_stream - find_start_song_stream)
                    elif find_start_song_stream == 0:
                        print('2', (find_stop_song_stream - find_start_song_stream) - (find_query_song_stream - find_start_song_stream))
                        t_time_s = 10
                    elif find_start_song_stream < find_stop_song_stream and find_start_song_stream != 0:
                        print('3', (find_stop_song_stream - find_start_song_stream) - (find_query_song_stream - find_start_song_stream))
                        t_time_s = (find_stop_song_stream - find_start_song_stream) - (find_query_song_stream - find_start_song_stream)
                    elif find_duration_song_stream == 0 and find_start_song_stream == find_stop_song_stream:
                        print('4', find_current_song_stream - find_query_song_stream)
                        t_time_s = 10
                    if t_time_s < 0:
                        t_time_s = 5
                    print('t_time_s ==>  In get_title_song_personal_station ', t_time_s)
                    chek = 3
                except HTTPError as e:
                    print('The server couldn\'t fulfill the request. In get_title_song_personal_station')
                    print('Error code In get_title_song_personal_station: ', e.code)
                    chek += 1
                except URLError as e:
                    print('We failed to reach a server. In get_title_song_personal_station')
                    print('Reason In get_title_song_personal_station: ', e.reason)
                    chek += 1
            self.timer_title_rtmp = GObject.timeout_add_seconds(t_time_s, self.get_title_song_personal_station, id_ch)
        else:
            if self.timer_title_rtmp:
                GObject.source_remove(self.timer_title_rtmp)
            return False

# Класс получения источника потока 101.RU
class HackURL(object):


    def __init__(self):

        self.used_stream_adress = []
        self.check_stream_adress = 0

    def hack_url_adres(self, adres):

        print('Получение адреса потока = ', adres)

        if 'personal' in adres:
            person = 1
        else:
            person = 0

        r101_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        r101_opener.addheaders = [
        ('Host', '101.ru'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
        ]

        try:
            print('Отправка запроса')
            with r101_opener.open(adres) as r101_http_source:
                html = r101_http_source.read().decode('utf-8', errors='ignore')
            if person == 0:
                find_url_stream = re.findall(r"'st'\:'/design/images/.+?\.st'\,'\w+'\:'(.+?)'\,'wheel'\:\d+", html, re.M)
            elif person == 1:
                find_url_stream = re.findall(r"(rtmp://.+?)///main", html, re.S)
                try:
                    res_rtmp_url = re.sub(r'\|', r'&', find_url_stream[0], re.S)+'/main'
                except IndexError:
                    res_rtmp_url = 0
                print('res_rtmp_url ==> ', res_rtmp_url)
                return res_rtmp_url
            if '.flv' in str(find_url_stream):
                '''http://f1.101.ru/api/getplayingtrackinfo.php?station_id=82&typechannel=channel'''
                return find_url_stream[0]
            if len(find_url_stream) >= 1:

                with r101_opener.open("http://101.ru/"+re.sub(r"\|", r"&", find_url_stream[0])+"-1") as r101_http_source2:
                    html2 = r101_http_source2.read().decode('utf-8', errors='ignore')

                print('Разбор запроса для заполнения find_url_stream')
                find_url_stream2 = re.findall(r'"file":"(.+?)"', str(html2), re.S)
                print('*********************************')
                print('*********************************')
                print('Count find_url_stream2 ', len(find_url_stream2))
                print('*********************************')
                print('*********************************')
                len_adr_list = 0
                for x in find_url_stream2:
                    print('req = urllib.request.Request(x)', x)
                    try:
                        with r101_opener.open(x, timeout=5) as req:
                            response = req
                    except:
                        print('ERROR : ', x)
                        len_adr_list += 1
                    else:
                        print('OK Response ==> \n', response.info())
                        if not x in self.used_stream_adress and self.check_stream_adress <= len(find_url_stream2):
                            print('self.check_stream_adress ==> ', self.check_stream_adress)
                            self.check_stream_adress += 1
                            self.used_stream_adress =[]
                            self.used_stream_adress.append(x)
                            return x
                    if len(find_url_stream2) == len_adr_list or self.check_stream_adress >= len(find_url_stream2):
                        print('Нет рабочих потоков')
                        self.check_stream_adress = 0
                        return 0
            else:
                print('ERROR in Requestion Page')
        except HTTPError as e:
            print('The server couldn\'t fulfill the request.')
            print('Error code: ', e.code)
        except URLError as e:
            print('We failed to reach a server.')
            print('Reason: ', e.reason)

class WriteLastStation(object):


    def __init__(self):

        self.dirty_date = ''
        self.wr_path = os.path.dirname(os.path.realpath(__file__))

        with open(self.wr_path + '/adres_list.ini', 'r', encoding='utf-8', errors='ignore') as main_param_file:
            self.dirty_date = main_param_file.read()

        self.dirty_list_date = re.sub(r'amp;', r'', self.dirty_date).split('\n')

        self.dict_name_adr = {}

        for x in self.dirty_list_date:
            if x != '':
                d = x.split(' = ')
                self.dict_name_adr[d[0]] = 'http://101.ru'+d[1]

        # Существуют ли записи предыдущих станций
        # Section in station.ini
        '''[LastStation][BestStatin]'''
        try:
            config = configparser.ConfigParser()

            config.read(
            os.path.dirname(os.path.realpath(__file__))+'/station.ini',
            encoding='utf-8')

            leq = config['LastStation']
        except:
            config = configparser.ConfigParser()
            config.add_section('LastStation')
            config.set('LastStation', 'addrstation', '')
            config.set('LastStation', 'namestation', '')
            config.add_section('BestStation')
            config.set('BestStation', 'addrstation', '')
            config.set('BestStation', 'namestation', '')
            with open(self.wr_path + '/station.ini', 'w') as cfgfile:
                config.write(cfgfile)

    def write_last_station(self, *args):

        if 'http' in ''.join(args[0]):
            print('HTTP WRITE ', ''.join(args[0]))
            adr = ''
            nam = ''
            for key in self.dict_name_adr:
                if self.dict_name_adr[key] == ''.join(args[0]):
                    adr = self.dict_name_adr[key]
                    nam = str(key)
            if nam != '':
                config = configparser.ConfigParser()
                config.read(os.path.dirname(os.path.realpath(__file__))+'/station.ini', encoding = 'utf-8')
                config.set('LastStation', 'addrstation', adr)
                if args[1][0] == 'PS':
                    config.set('LastStation', 'namestation', 'PS')
                elif args[1][0] == 'RREC':
                    config.set('LastStation', 'namestation', 'Radio-Record')
                elif args[1][0] == 'RTUN':
                    config.set('LastStation', 'namestation', 'RadioTun')
                elif args[1][0] == 'My':
                    config.set('LastStation', 'namestation', 'My')
                elif args[1][0] == 'DI':
                    config.set('LastStation', 'namestation', 'D-FM')
                elif args[1][0] == 'IRC':
                    config.set('LastStation', 'namestation', 'Internet Radio COM')
                else:
                    config.set('LastStation', 'namestation', nam)
            else:
                config = configparser.ConfigParser()

                config.read(
                os.path.dirname(os.path.realpath(__file__))+'/station.ini',
                encoding = 'utf-8')

                config.set('LastStation', 'addrstation', ''.join(args[0]))
                if args[1][0] == 'PS':
                    config.set('LastStation', 'namestation', 'PS')
                elif args[1][0] == 'My':
                    config.set('LastStation', 'namestation', 'My')
                elif args[1][0] == 'RREC':
                    config.set('LastStation', 'namestation', 'Radio-Record')
                elif args[1][0] == 'RTUN':
                    config.set('LastStation', 'namestation', 'RadioTun')
                elif args[1][0] == 'DI':
                    config.set('LastStation', 'namestation', 'D-FM')
                elif args[1][0] == 'IRC':
                    config.set('LastStation', 'namestation', 'Internet Radio COM')
                else:
                    config.remove_option('LastStation', 'namestation')
            with open(self.wr_path + '/station.ini', 'w', encoding = 'utf-8') as configfile:
                config.write(configfile)
        elif 'rtmp' in ''.join(args[0]):
            print('RTMP WRITE ', ''.join(args[0]))
            config = configparser.ConfigParser()
            config.read(os.path.dirname(os.path.realpath(__file__))+'/station.ini', encoding = 'utf-8')
            config.set('LastStation', 'addrstation', ''.join(args[0]))
            if args[1][0] == 'PS':
                config.set('LastStation', 'namestation', 'PS')
            elif args[1][0] == 'My':
                config.set('LastStation', 'namestation', 'My')
            elif args[1][0] == 'DI':
                config.set('LastStation', 'namestation', 'D-FM')
            elif args[1][0] == 'IRC':
                config.set('LastStation', 'namestation', 'Internet Radio COM')
            else:
                config.remove_option('LastStation', 'namestation')
            with open(self.wr_path + '/station.ini', 'w', encoding = 'utf-8') as configfile:
                config.write(configfile)

    def write_best_station(self, *args):

        print('def write_best_station(self, *args): ==> ', ''.join(args[0][0]))

        take_param_adr = 0

        def find_key(x):
            if x == 1:
                res = args[0][1]
                return res
            elif x == 2:
                res = args[0][1][0]
                return res
            else:
                pass

        for c in range(1, 4):
            if str(type(find_key(c))) != "<class 'list'>" and str(type(find_key(c))) != "<class 'tuple'>":
                take_param_adr = find_key(c)
                break
            else:
                pass

        print('take_param_adr ++++++++++++++++++++=> ', take_param_adr)
        str_name_chanel = ''
        try:
            print(' 1 "".join(args)  ++++++++++++++++++++=> ', ''.join(args))
            str_adr_chanel = ''.join(args)
        except:
            print(' 2 "".join(args[0][0])  ++++++++++++++++++++=> ', ''.join(args[0][0]))
            str_adr_chanel = ''.join(args[0][0])
        print("if 'http' in str(str_adr_chanel): =-=-=> ", str_adr_chanel)
        if 'http' in str(str_adr_chanel):
            adr = ''
            nam = ''
            try:
                for key in self.dict_name_adr:
                    if self.dict_name_adr[key] == str(str_adr_chanel):
                        print('self.dict_name_adr[key], str_adr_chanel ', self.dict_name_adr[key], str_adr_chanel, key)
                        adr = self.dict_name_adr[key]
                        nam = key
                        print('SET = adr, nam', adr, nam)
            except:
                adr = str_adr_chanel
            print('adr & nam & take_param_adr', '(', adr, ')', '(', nam, ')', '(', take_param_adr, ')')
            if adr == '':
                adr = str_adr_chanel
            config = configparser.ConfigParser()

            config.read(
            os.path.dirname(os.path.realpath(__file__))+'/station.ini',
            encoding = 'utf-8')

            config.set('BestStation', 'addrstation', adr)
            print('nam ==> ', nam)
            print('take_param_adr ==> ', type(take_param_adr), take_param_adr)
            if nam == '':
                if take_param_adr in 'PS':
                    config.set('BestStation', 'namestation', 'PS')
                elif take_param_adr in 'My':
                    config.set('BestStation', 'namestation', 'My')
                elif take_param_adr in 'RREC':
                    config.set('BestStation', 'namestation', 'Radio-Record')
                elif take_param_adr in 'RTUN':
                    config.set('BestStation', 'namestation', 'RadioTun')
                elif take_param_adr in 'DI':
                    config.set('BestStation', 'namestation', 'D-FM')
                elif take_param_adr in 'IRC':
                    config.set('BestStation', 'namestation', 'Internet Radio COM')
            else:
                config.set('BestStation', 'namestation', nam)
            with open(self.wr_path + '/station.ini', 'w', encoding = 'utf-8') as configfile:
                config.write(configfile)
        elif 'rtmp' in str_adr_chanel:
            config = configparser.ConfigParser()

            config.read(
            os.path.dirname(os.path.realpath(__file__))+'/station.ini',
            encoding = 'utf-8')

            config.set('BestStation', 'addrstation', str_adr_chanel)
            if take_param_adr in 'PS':
                config.set('BestStation', 'namestation', 'PS')
            elif take_param_adr in 'My':
                config.set('BestStation', 'namestation', 'My')
            elif take_param_adr in 'RREC':
                config.set('BestStation', 'namestation', 'Radio-Record')
            elif take_param_adr in 'RTUN':
                config.set('BestStation', 'namestation', 'RadioTun')
            elif take_param_adr in 'DI':
                config.set('BestStation', 'namestation', 'D-FM')
            elif take_param_adr in 'IRC':
                config.set('BestStation', 'namestation', 'Internet Radio COM')
            else:
                config.remove_option('BestStation', 'namestation')
            with open(self.wr_path + '/station.ini', 'w', encoding = 'utf-8') as configfile:
                config.write(configfile)

    def read_last_station(self, *args):

        config = configparser.ConfigParser()

        config.read(
        os.path.dirname(os.path.realpath(__file__))+'/station.ini',
        encoding = 'utf-8')

        adr = config['LastStation']
        return adr.get('addrstation'), adr.get('namestation')

    def read_best_station(self, *args):

        config = configparser.ConfigParser()

        config.read(
        os.path.dirname(os.path.realpath(__file__))+'/station.ini',
        encoding = 'utf-8')

        adr = config['BestStation']
        return adr.get('addrstation'), adr.get('namestation')

# Диалог поиска персональных станций
class DialogFindPersonalStation(Gtk.Dialog):


    def __init__(self, parent):

        Gtk.Dialog.__init__(self,
        "Find Personal station", parent, Gtk.DialogFlags.MODAL)

        self.connect('close', self.close_dial_win)
        self.connect('destroy', self.close_dial_win)
        self.connect('destroy-event', self.close_dial_win)

        self.set_default_size(400, 100)
        self.hurl = HackURL()

        self.s_find_dict = {}
        self.s_res_find_name = []
        self.return_adres = ''

        # Первая (основная сетка размещения)
        box = self.get_content_area()

        self.s_grid = Gtk.Grid()
        self.s_grid.set_border_width(5)

        self.s_entry = Gtk.Entry()
        self.s_entry.set_icon_from_stock(
        Gtk.EntryIconPosition.SECONDARY, Gtk.STOCK_FIND)

        self.s_entry.connect('icon-press', self.key_icon_press)
        self.s_entry.connect('key-release-event', self.key_icon_press)

        self.s_grid.attach(self.s_entry, 0, 1, 8, 1)

        self.s_liststore = Gtk.ListStore(str, bool)

        self.s_treeview = Gtk.TreeView(model=self.s_liststore)
        self.s_treeview.set_enable_search(True)
        self.s_treeview.set_show_expanders(False)

        s_renderer_text = Gtk.CellRendererText()
        self.s_column_text = Gtk.TreeViewColumn("Станция", s_renderer_text, text=0)
        self.s_column_text.set_alignment(0.5)
        self.s_column_text.set_max_width(270)
        self.s_column_text.set_min_width(50)
        self.s_column_text.set_fixed_width(270)
        self.s_column_text.set_resizable(False)
        self.s_column_text.set_expand(False)

        self.s_treeview.append_column(self.s_column_text)

        s_renderer_radio = Gtk.CellRendererToggle()
        s_renderer_radio.set_radio(True)
        s_renderer_radio.connect("toggled", self.s_on_cell_radio_toggled)

        self.s_column_radio = Gtk.TreeViewColumn("Выбор", s_renderer_radio, active=1)
        self.s_column_radio.set_alignment(0.5)
        self.s_column_radio.set_resizable(False)
        self.s_column_radio.set_expand(False)

        self.s_treeview.append_column(self.s_column_radio)

        # Создание окна с прокруткой для размещения в нем List
        self.s_scrolled_window = Gtk.ScrolledWindow()
        self.s_scrolled_window.set_min_content_height(200)
        self.s_scrolled_window.set_min_content_width(340)
        self.s_scrolled_window.add(self.s_treeview)

        self.s_grid.attach(self.s_scrolled_window, 0, 2, 8, 10)
        self.s_grid.set_column_homogeneous(True)# Ровнять
        self.s_grid.set_row_homogeneous(True)
        self.s_grid.set_column_spacing(5)

        box.add(self.s_grid)
        self.show_all()

    def key_icon_press(self, *args):

        try:
            k_val = args[1].keyval
        except AttributeError:
            k_val = 65293
        if k_val == 65293 and self.s_entry.get_text() != '':
            self.find_icon_press()
            return True

    def close_dial_win(self, *args):

        self.response(-7)
        self.destroy()

    def s_on_cell_radio_toggled(self, widget, path):

        self.hide()
        selected_path = Gtk.TreePath(path)
        c = self.s_liststore.get_iter(path)
        for x in self.s_res_find_name:
            if str(x) == str(self.s_liststore.get_value(c, 0)):
                print('----------------------------------------')
                print(self.s_liststore.get_value(c, 0))
                print(self.s_find_dict.get(str(x)))
                print('----------------------------------------')
                self.return_adres = self.hurl.hack_url_adres(self.s_find_dict.get(str(x)))
        for row in self.s_liststore:
            row[1] = (row.path == selected_path)
        self.response(-5)


    def find_icon_press(self, *args):

        #
        find_pers_101_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        find_pers_101_opener.addheaders = [
        ('Host', '101.ru'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
        ]
        #
        self.s_find_dict = {}
        self.s_liststore.clear()
        self.s_treeview.remove_column(self.s_column_text)
        self.s_treeview.remove_column(self.s_column_radio)
        self.s_treeview.append_column(self.s_column_text)
        self.s_treeview.append_column(self.s_column_radio)
        zapros = urllib.parse.quote(self.s_entry.get_text(), encoding='utf-8', errors=None)
        adr_req = 'http://101.ru/?an=port_search_pers&search='+str(zapros)
        #
        with find_pers_101_opener.open(adr_req) as pers_101:
            sourse = re.sub(r'(&#\d+;)', r'', pers_101.read().decode('utf-8', errors='ignore'), re.S)
            res_error = re.findall(r'<h3 class="full">(.+?)</h3>', sourse)
            self.s_res_find_name = re.findall(r'<h2 class="title"><a href=".+?">(.+?)</a></h2>', re.sub(r'&amp;|&quot;|&#\d+?;', r'&', sourse, re.S), re.S)
            res_find_adr = re.findall(r'<h2 class="title"><a href="(.+?)">.+?</a></h2>', sourse, re.S)
        if not res_error:
            c = 0
            for x in sorted(self.s_res_find_name):
                self.s_find_dict[x] = 'http://101.ru'+re.sub(r'(&amp;|&#\d+;)', r'&', res_find_adr[c], re.S)
                self.s_liststore.append([str(x), False])
                c += 1
        else:
            self.s_liststore.append([str(res_error[0]), False])

# Диалог ввода пользовательского адреса интернет радио
class DialogEntryAdr(Gtk.Dialog):


    def __init__(self, parent):

        Gtk.Dialog.__init__(self,
        "Воспроизвести пользовательский адрес",
        parent,
        Gtk.DialogFlags.MODAL,
        (Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL,
        Gtk.STOCK_OK, Gtk.ResponseType.OK))

        self.set_default_size(350, 100)

        label = Gtk.Label("Введите адрес...")

        self.entry = Gtk.Entry()

        box = self.get_content_area()
        box.add(label)
        box.add(self.entry)
        self.show_all()

# Диалог создания адресного листа для IRC
class DialogC_A_L(Gtk.Dialog):

    def close_status(self, *args):

        self.c_s = True
        if args[1] == -4 or args[1] == -7:
            self.destroy()

    def c_a_l(self):
        #
        self.IRC_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        self.IRC_opener.addheaders = [
        ('Host', 'www.internet-radio.com'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
        ]
        #

        def m_m(x):
            self.main_progress.set_fraction(x[0])
            self.main_progress.set_text(x[1])

        def read_page_irc(args):

            with self.IRC_opener.open('http://www.internet-radio.com/stations/'+re.sub(r' ', r'%20', args[0])+'/page'+str(args[1])) as req:
                s_page_r = req.read().decode('utf-8', errors='ignore')
                fr = re.findall(r"mount=(.+?)&amp;title=(.+?)&amp;", s_page_r, re.M)
                res_dict[x] = fr

            for e in fr:
                self.line_to_write.append(re.sub(r'\s+$', r'', str(e[1]), re.S)+' = '+re.sub(r'\/live\.m3u', r'/live', re.sub(r'\/listen\.pls', r'/;', re.sub(r'\/listen\.pls\?sid\=1', r'/;', re.sub(r'\.m3u', r'', re.sub(r'^=\s*', r'', str(e[0]), re.M), re.M), re.M), re.M), re.M))

            mm_m = []
            mm_m.append(float(m_check//(len(choice_page)/100)) / 100)
            mm_m.append(str(int(m_check//(len(choice_page)/100)))+' %')
            GLib.idle_add(m_m, mm_m)

        res_dict = {}
        pat = ['^\s+', '^\s*\-\s*', ':{2,}', '^\s*\=+\s*', '^\s*\:+\s*']
        if self.my_args[0] == 1:
            with self.IRC_opener.open('http://www.internet-radio.com') as for_short_name:
                page_short_name = for_short_name.read().decode('utf-8', errors='ignore')
                ptrn_s = '''<li><a onClick\="ga\('send'\, 'event'\, 'genreclick'\, 'navbar'\, '.+?'\)\;" href\=".+?">(.+?)</a></li>'''
                short_sum_page = [x for x in re.findall(r''+str(ptrn_s)+'', page_short_name, re.M)]
                choice_page = short_sum_page
        elif self.my_args[0] == 2:
            with self.IRC_opener.open('http://www.internet-radio.com/stations/') as for_full_name:
                full_page_name = for_full_name.read().decode('utf-8', errors='ignore')
                ptrn_f = '''<dt class="text\-capitalize" style="font\-size\: .+?\;"><a href=".+?">(.+?)</a></dt>'''
                full_sum_page = [x for x in re.findall(r''+str(ptrn_f)+'', full_page_name, re.M)]
                choice_page = full_sum_page
        m_check = 1
        with open(self.dial_path + '/radiointernet.txt', 'w', encoding = 'utf-8') as file_d:

            for x in choice_page:

                with self.IRC_opener.open('http://www.internet-radio.com/stations/'+re.sub(r' ', r'%20', x)+'/') as ar:
                    page_r = ar.read().decode('utf-8', errors='ignore')

                sum_page = [int(j) for j in re.findall(r'href="/stations/.+?/page\d+">(\d+)</a>', page_r, re.M)]

                if m_check == 0:
                    self.line_to_write.append('['+x+']\n')
                else:
                    self.line_to_write.append('\n['+x+']\n')

                if len(sum_page) == 0:
                    sum_page = [1]

                with concurrent.futures.ThreadPoolExecutor(max_workers=1000) as executor:
                    future_to_url = {executor.submit(read_page_irc, (x, f)): f for f in range(0, max(sum_page))}
                    for future in concurrent.futures.as_completed(future_to_url):
                        pass
                m_check += 1
            for h in list(OrderedDict.fromkeys(self.line_to_write)):
                d_part = h
                for o_d in range(len(pat)):
                    d_part = re.sub(pat[o_d], r'', d_part, re.S)
                file_d.write(d_part+'\n')
            self.response(22)

    def __init__(self, parent, *args):

        Gtk.Dialog.__init__(self, "Создание адресного листа для IRC", parent, Gtk.DialogFlags.MODAL)

        self.connect('response', self.close_status)

        self.c_s = False

        self.line_to_write = []

        self.my_args = args
        self.dial_path = os.path.dirname(os.path.realpath(__file__))

        self.main_progress = Gtk.ProgressBar(show_text=True)

        self.box = self.get_content_area()
        self.box.add(self.main_progress)
        self.set_border_width(1)
        self.set_default_size(350, 20)
        self.show_all()

        threadm = threading.Thread(target=self.c_a_l, daemon=True)
        threadm.start()

        # Удаление пустых секций
        fin_config = configparser.ConfigParser(delimiters=('='), allow_no_value=True, strict=False)
        fin_config.read(os.path.dirname(os.path.realpath(__file__))+'/radiointernet.txt', encoding = 'utf-8')
        all_sections = fin_config.sections()

        for x in all_sections:
            if len(fin_config.options(x)) == 0:
                fin_config.remove_section(x)

        with open(os.path.dirname(os.path.realpath(__file__))+'/radiointernet.txt', 'w', encoding='utf-8') as configfile:
            fin_config.write(configfile)

# Диалог отображения эквалайзера
class EQWindow(Gtk.Dialog):


    def __init__(self, parent):

        Gtk.Dialog.__init__(self, "EQ", parent, Gtk.DialogFlags.MODAL,
            (Gtk.STOCK_CANCEL, Gtk.ResponseType.CANCEL,
             Gtk.STOCK_OK, Gtk.ResponseType.OK))

        self.set_default_size(250, 250)
        self.eq_path = os.path.dirname(os.path.realpath(__file__))

        self.mdict = []
        self.arr_eq = []

        self.name_combo = Gtk.ComboBoxText()
        self.name_combo.connect("changed", self.on_currency_combo_changed)
        self.name_combo.set_entry_text_column(0)

        # Установлен эквалайзер или нет
        try:
            test_config = configparser.ConfigParser()
            test_config.read(os.path.dirname(os.path.realpath(__file__))+'/set-eq.ini', encoding='utf-8')
            leq = test_config['EQ-Settings']['lasteq'].split(' ')
            for x in leq:
                self.mdict.append(x)
            for x in test_config.items('EQ-Settings'):
                self.name_combo.append_text(str(x[0]))
        except:
            test_config = configparser.ConfigParser()
            test_config.add_section('EQ-Settings')
            test_config.set('EQ-Settings','lasteq','0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0')
            with open(self.eq_path + '/set-eq.ini', 'w') as cfgfile:
                test_config.write(cfgfile)
            test_config.read(os.path.dirname(os.path.realpath(__file__))+'/set-eq.ini', encoding='utf-8')
            for x in test_config.items('EQ-Settings'):
                self.name_combo.append_text(str(x[0]))
            leq = test_config['EQ-Settings']['lasteq'].split(' ')
            for x in leq:
                self.mdict.append(x)

        self.m_freq = ['16Hz','20Hz','60Hz','120Hz','200Hz','250Hz',
        '400Hz','500Hz','800Hz','1kHz','2kHz','3kHz','4kHz','5kHz',
        '6kHz','10kHz','12kHz','16kHz']
        # Основная шкала для ползунков эквалайзеров
        self.scale_n = {36:'-24', 35:'-23',34:'-22',33:'-21',32:'-20',31:'-19',
        30:'-18',29:'-17',28:'-16',27:'-15',26:'-14',25:'-13',24:'-12',23:'-11',
        22:'-10',21:'-9',20:'-8',19:'-7',18:'-6',17:'-5',16:'-4',15:'-3',
        14:'-2',13:'-1',12:'0',11:'1',10:'2',9:'3',8:'4',7:'5',6:'6',5:'7',
        4:'8',3:'9',2:'10',1:'11',0:'12'}

        self.box = self.get_content_area()

        self.grid_w_eq = Gtk.Grid()
        self.grid_w_eq.set_border_width(5)
        self.box.add(self.grid_w_eq)

        self.grid_edit = Gtk.Grid()
        self.grid_edit.set_border_width(5)

        self.sc_l = [Gtk.Scale.new_with_range(Gtk.Orientation.VERTICAL, 0, 36, 0.1) for x in range(18)]
        self.label_l = [Gtk.Label() for x in range(18)]
        self.label_Hz = [Gtk.Label.new(str(self.m_freq[x])) for x in range(18)]

        # Создание кнопки Сохранить Установить
        self.button_save = Gtk.Button()
        self.button_save.set_relief(Gtk.ReliefStyle.HALF)
        self.button_save.set_resize_mode(Gtk.ResizeMode.PARENT)
        self.button_save.set_alignment(0.5, 0.5)
        self.button_save.connect("clicked", self.ret_md)

        # Создание иконок из стока для кнопки
        self.button_to_null = Gtk.Button('Обноулить')
        self.button_to_null.set_relief(Gtk.ReliefStyle.HALF)
        self.button_to_null.set_resize_mode(Gtk.ResizeMode.PARENT)
        self.button_to_null.set_alignment(0.5, 0.5)
        self.button_to_null.connect("clicked", self.all_null)

        self.name_entry = Gtk.Entry()
        self.timeout_id = GObject.timeout_add(500, self.chenge_bat_label)

        self.grid_edit.attach(self.button_to_null, 0, 1, 4, 1)

        self.grid_edit.attach(self.name_combo, 4, 1, 4, 1)
        self.grid_edit.attach(self.name_entry, 8, 1, 4, 1)
        self.grid_edit.attach(self.button_save, 12, 1, 4, 1)

        self.grid_edit.set_row_homogeneous(True)
        self.grid_edit.set_column_homogeneous(True)
        self.grid_edit.set_row_spacing(2)
        self.grid_edit.set_column_spacing(3)

        self.grid_w_eq.attach(self.grid_edit, 0, 1, 18, 1)

        c = 0
        for x in self.sc_l:
            x.set_draw_value(False)
            x.set_value_pos(Gtk.PositionType.TOP)
            x.set_has_origin(True)
            for k, v in self.scale_n.items():
                if self.mdict[c] == v:
                    self.label_l[c].set_label(v)
                    x.set_value(float(k))
            x.connect("change-value", self.write_arr_in)
            self.grid_w_eq.attach(self.label_l[c], c, 2, 1, 1)
            self.grid_w_eq.attach(x, c, 3, 1, 10)
            self.label_Hz[c].modify_bg(Gtk.StateType.NORMAL, Gdk.Color.from_floats(0.9, 0.9, 0.95))
            self.grid_w_eq.attach(self.label_Hz[c], c, 14, 1, 1)
            c += 1

        self.grid_w_eq.set_column_homogeneous(True)
        self.grid_w_eq.set_row_homogeneous(False)
        self.grid_w_eq.set_row_spacing(20)
        self.grid_w_eq.set_column_spacing(1)

        self.show_all()

    # Изменение надписи на кнопке
    def chenge_bat_label(self, *args):

        if self.name_entry.get_text() != '':
            self.button_save.set_label('Сохранить настройки')
        else:
            self.button_save.set_label('Установить по умолчанию')
        return True

    # Изменение положения ползунков
    def on_currency_combo_changed(self, combo):

        combo_config = configparser.ConfigParser()
        combo_config.read(os.path.dirname(os.path.realpath(__file__))+'/set-eq.ini', encoding='utf-8')
        self.arr_eq = []
        text = combo.get_active_text()
        if text != None:
            print("Selected: currency=%s" % text)
            leq = combo_config['EQ-Settings'][text].split(' ')
            for x in leq:
                self.arr_eq.append(x)
            print('self.arr_eq', self.arr_eq)
            c = 0
            for x in self.sc_l:
                for k, v in self.scale_n.items():
                    if str(self.arr_eq[c]) == v:
                        self.label_l[c].set_label(v)
                        x.set_value(int(k))
                c += 1

    # Все эквалайзеры на ноль
    def all_null(self, *args):

        c = 0
        for x in self.sc_l:
            self.label_l[c].set_label('0')
            x.set_value(float(12))
            c += 1

    # Запись результата настроек в файл
    def write_cfg_prs(self, *args):

        wr_config = configparser.ConfigParser()
        wr_config.read(os.path.dirname(os.path.realpath(__file__))+'/set-eq.ini', encoding='utf-8')

        if len(self.arr_eq) != 18:
            if self.name_entry.get_text() != '':
                print('Есть текст в интри')
                lasteq = self.name_entry.get_text()
                wr_config.set('EQ-Settings', lasteq, ' '.join(self.mdict))
                with open(self.eq_path + '/set-eq.ini', 'w', encoding = 'utf-8', errors='ignore') as configfile:
                    wr_config.write(configfile)
            elif self.name_entry.get_text() == '':
                print('Нет текста в интри')
                lasteq = 'lasteq'
                try:
                    wr_config.set('EQ-Settings', lasteq, ' '.join(self.mdict))
                    with open(self.eq_path + '/set-eq.ini', 'w', encoding = 'utf-8', errors='ignore') as configfile:
                        wr_config.write(configfile)
                except:
                    wr_config.add_section('EQ-Settings')
                    wr_config.set('EQ-Settings', lasteq, ' '.join(self.mdict))
                    with open(self.eq_path + '/set-eq.ini', 'w') as configfile:
                        wr_config.write(configfile)
        elif len(self.arr_eq) == 18:
            self.mdict = self.arr_eq
            if self.name_entry.get_text() != '':
                lasteq = self.name_entry.get_text()
            else:
                lasteq = 'lasteq'
            wr_config.set('EQ-Settings', lasteq, str(' '.join(self.arr_eq)))
            with open(self.eq_path + '/set-eq.ini', 'w', encoding = 'utf-8', errors='ignore') as configfile:
                wr_config.write(configfile)

    # Реакция на нажатие кнопки "Установить / Сохранить"
    def ret_md(self, *args):

        if self.name_entry.get_text() != '':
            self.name_combo.append_text(self.name_entry.get_text())
        self.mdict = []
        for x in self.sc_l:
            self.mdict.append(self.scale_n.get(int(x.get_value())))

        if len(self.arr_eq) == 18:
            self.mdict = self.arr_eq
        self.write_cfg_prs()

    # Запись результата настроек в массив self.mdict
    def write_arr_in(self, *value):

        for x in range(18):
            if round(self.sc_l[x].get_value()) == round(value[2]):
                self.label_l[x].set_label(self.scale_n.get(round(value[2])))
                self.mdict[x] = self.scale_n.get(round(value[2]))

# Класс Записи потока
class RecorderBin(Gst.Bin):

    def __init__(self, location):

        self.rec_pipeline = self.create_rec_pipeline(location)

        message_bus = self.rec_pipeline.get_bus()
        message_bus.add_signal_watch_full(1)
        message_bus.connect('message', self.message_handler)

        #self.rec_pipeline.set_state(Gst.State.PLAYING)

    def list_files(self, path):

        name_files = []
        for name in os.listdir(path):
            if os.path.isfile(os.path.join(path, name)):
                if 'new' in name:
                    name_files.append(name)

        files_list = sorted(name_files)

        try:
            d_name = re.findall(r'(^\d+)(.+?)$', files_list[-1])
        except IndexError:
            d_name = [(0, '_new.ogg')]

        return str(int(d_name[0][0])+1)+str(d_name[0][1])

    def create_rec_pipeline(self, location):

        def on_pad_added(decodebin, pad):
            pad.link_full(self.rec_audioconvert.get_static_pad('sink'), Gst.PadLinkCheck.TEMPLATE_CAPS)

        rec_pipeline = Gst.Pipeline()
        '''
        uridecodebin uri=http://air.radiorecord.ru:8102/club_320 !
        audioconvert !
        vorbisenc !
        oggmux !
        filesink location=1_new.ogg
        '''

        self.rec_uridecodebin = Gst.ElementFactory.make('uridecodebin', 'uridecodebin')
        self.rec_audioconvert = Gst.ElementFactory.make('audioconvert', 'audioconvert')
        self.rec_vorbisenc = Gst.ElementFactory.make("vorbisenc", "vorbisenc")
        self.rec_oggmux = Gst.ElementFactory.make("oggmux", "oggmux")
        self.rec_filesink = Gst.ElementFactory.make("filesink", "filesink")

        self.rec_uridecodebin.connect('pad-added', on_pad_added)
        self.rec_vorbisenc.set_property('managed', True)
        self.rec_vorbisenc.set_property('quality', 0.9)
        self.rec_uridecodebin.set_property('uri', location)
        self.rec_filesink.set_property("location", self.list_files(os.path.dirname(os.path.realpath(__file__))))

        [rec_pipeline.add(k) for k in [self.rec_vorbisenc, self.rec_oggmux,
        self.rec_filesink, self.rec_uridecodebin, self.rec_audioconvert]]

        print('REC-Linck №1 OK', self.rec_audioconvert.link(self.rec_vorbisenc))
        print('REC-Linck №2 OK', self.rec_vorbisenc.link(self.rec_oggmux))
        print('REC-Linck №3 OK', self.rec_oggmux.link(self.rec_filesink))

        return rec_pipeline

    def message_handler(self, bus, message):

        if message.type == Gst.MessageType.EOS:
            print('End Of Stream for rec_pipeline')
            self.rec_pipeline.set_state(Gst.State.NULL)


class Dialog_Update_101(Gtk.Dialog):

    def update_progess(self, fr):
        self.progress_101_update.set_fraction(float(fr/100))
        self.progress_101_update.set_text(str(int(fr))+' %')
        return False

    def example_target(self, args1, stop_event):

        loc_ad_101_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
        loc_ad_101_opener.addheaders = [
        ('Host', '101.ru'),
        ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
        ]

        # Запрос всех разделов
        with loc_ad_101_opener.open('http://101.ru/?an=port_allchannels') as loc_source_101_http:
            loc_razdel_101_http = re.findall(r'<li class\="h4 tab\-item "><a href\="(.+?)">(.+?)<\/a><\/li>', loc_source_101_http.read().decode('utf-8', errors='ignore'), re.M)

        percent = len(loc_razdel_101_http)
        check = 1
        for x, y in loc_razdel_101_http:
            a = []
            with loc_ad_101_opener.open('http://101.ru'+re.sub(r'amp;', r'', x, re.M)) as loc_source_101_razdel:
                loc_source_101_http_razdel = re.findall(r'<h2 class\="title"><a href\="(.+?)">(.+?)<\/a><\/h2>', loc_source_101_razdel.read().decode('utf-8', errors='ignore'), re.M)
                for z, c in loc_source_101_http_razdel:
                    a.append(c+' = '+re.sub(r'amp;', r'', z, re.M))
                self.loc_dict_101_ru.append(a)

                if not stop_event.is_set():
                    GLib.idle_add(self.update_progess, check//(percent/100))
                else:
                    return False

                check += 1

        self.response(-4)

    def __init__(self, parent):

        Gtk.Dialog.__init__(self,
        "Обновление адресного листа для 101.RU",
        parent,
        Gtk.DialogFlags.MODAL)

        self.loc_dict_101_ru = []

        self.set_default_size(400, 30)

        self.progress_101_update = Gtk.ProgressBar(show_text=True)

        box = self.get_content_area()
        box.add(self.progress_101_update)
        self.show_all()

        self.thread_3_stop = threading.Event()
        self.thread_3 = threading.Thread(target=self.example_target, args=(1, self.thread_3_stop), daemon=True)
        self.thread_3.start()


def download_up_date():

    my_path_up = os.path.dirname(os.path.realpath(__file__))

    update_prog_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
    update_prog_opener.addheaders = [
    ('Host', 'github.com'),
    ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')
    ]

    # Загрузка архива
    with update_prog_opener.open('https://github.com/IvSatel/Player101ru/archive/master.zip') as source_up_zip:
        with open(my_path_up + '/master.zip', 'wb') as myzip:
            myzip.write(source_up_zip.read())

    # Проверка на существование пути
    def assure_path_exists(path):

        s_dir = os.path.dirname(path)
        # Если нет то создать
        if not os.path.exists(s_dir):
            os.mkdir(s_dir)

    # Открыть файл архива
    with zipfile.ZipFile(my_path_up + '/master.zip') as my_z_file:

        # Итерируем имена в архиве
        for x in my_z_file.namelist():

            # Удаляем корневую папку в архиве
            if x.replace('Player101ru-master', '') != '':

                # Читаем файлы в архиве
                f = my_z_file.read(x)

                # Создаем структуру папок
                dir_mp = re.sub(r'//$', r'/', str(my_path_up +'/'+ x.replace('Player101ru-master', '')))

                # Если прочитано 0 то значит это папка
                if len(f) == 0:
                    assure_path_exists(dir_mp)
                else:
                    # Если прочитано не 0 то записываем на диск
                    with open(dir_mp, 'wb') as w_f:
                        w_f.write(f)

    # Удаляем скаченый файл архива
    os.remove(my_path_up + '/master.zip')

def main_funck():
    # Проверка версии
    version_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
    version_opener.addheaders = [('Host', 'raw.githubusercontent.com'),
    ('Accept', 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8'),
    ('Accept-Language', 'ru-RU,ru;q=0.8,en-US;q=0.5,en;q=0.3'),
    ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

    remote_vers = ''

    with version_opener.open('https://raw.githubusercontent.com/IvSatel/Player101ru/master/version') as fo:
        remote_vers = fo.read().decode()

    if SCRIPT_VERSION < remote_vers or not os.path.exists(os.path.dirname(os.path.realpath(__file__)) +'/resource'):

        download_up_date()

        subprocess.Popen((sys.executable, os.path.abspath(__file__)), shell=False, stdout=None, stdin=None, stderr=subprocess.STDOUT)
        sys.exit()

    else:

        Radio_for_101 = RadioWin()
        Radio_for_101.connect("delete-event", Gtk.main_quit)
        Radio_for_101.show_all()
        Radio_for_101.seek_line.hide()
        Radio_for_101.playlist_scrolled_window.hide()

        for x in range(6):
            if x == 5:
                Radio_for_101.button_array[x].hide()

        GObject.threads_init()
        Gtk.main()

# Диалог вывода сообщения об отсутствии соединения с интернет
def check_internet_connection(*args):

    dialog = Gtk.MessageDialog(Gtk.Window(), 0, Gtk.MessageType.ERROR,
        Gtk.ButtonsType.OK, "Ошибка!")
    dialog.format_secondary_text(
        "Соединение с интернет не обнаружено\nпрограмма будет закрыта.")
    dialog.run()
    dialog.destroy()

# Проверка наличия интернет соединения
try:

    ftest_opener = urllib.request.build_opener(IF_PROXI, AUTHHANDLER, MY_COOKIE)
    ftest_opener.addheaders = [
    ('Host', 'www.google.ru'),
    ('User-agent', 'Mozilla/5.0 (X11; Ubuntu; Linux i686; rv:39.0) Gecko/20100101 Firefox/39.0')]

    with ftest_opener.open('http://www.google.ru/', timeout=5) as check_connection:
        print('Соединение с интернет обнаружено ' + str(datetime.datetime.now().strftime('%H:%M:%S')))
        main_funck()
except HTTPError as e:
    print('HTTPError The server couldn\'t fulfill the request.', e.code)
    check_internet_connection()
    sys.exit(0)
except URLError as e:
    print('URLError We failed to reach a server.', e.reason)
    check_internet_connection()
    sys.exit(0)
