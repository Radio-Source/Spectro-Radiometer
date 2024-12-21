#!/usr/bin/env python3
# -*- coding: utf-8 -*-

#
# SPDX-License-Identifier: GPL-3.0
#
# GNU Radio Python Flow Graph
# Title: Spectro Radiometer
# Author: smrt
# GNU Radio version: 3.10.9.2

from PyQt5 import Qt
from gnuradio import qtgui
from PyQt5 import QtCore
from PyQt5.QtCore import QObject, pyqtSlot
from gnuradio import blocks
from gnuradio import eng_notation
from gnuradio import fft
from gnuradio.fft import window
from gnuradio import filter
from gnuradio import gr
from gnuradio.filter import firdes
import sys
import signal
from PyQt5 import Qt
from argparse import ArgumentParser
from gnuradio.eng_arg import eng_float, intx
import SpectroRadiometer_helper as helper  # embedded python module
import math
import numpy as np
import osmosdr
import time
import sip
import threading



class SpectroRadiometer(gr.top_block, Qt.QWidget):

    def __init__(self, abw=4.0e6, antenna='RX2', baseline=20, bbgain=5, clock='default', dcg=100, decfile="", decln=0, device="rtl=0 file=/dev/zero,rate=2.50e6", dfreq=0.0, fbsize=128, fftsize=2048, frequency=1420.4058e6, gain=30, ifgain=5, integration=0.5, latitude=44.9, longitude=(-76.03), mode="total", ppstime='internal', prefix="h1", psrmode=0, ra=12.0, rfilist="", spec_interval=15, srate=2.50e6, tp_interval=2, zerofile="", zerotime=99.3):
        gr.top_block.__init__(self, "Spectro Radiometer", catch_exceptions=True)
        Qt.QWidget.__init__(self)
        self.setWindowTitle("Spectro Radiometer")
        qtgui.util.check_set_qss()
        try:
            self.setWindowIcon(Qt.QIcon.fromTheme('gnuradio-grc'))
        except BaseException as exc:
            print(f"Qt GUI: Could not set Icon: {str(exc)}", file=sys.stderr)
        self.top_scroll_layout = Qt.QVBoxLayout()
        self.setLayout(self.top_scroll_layout)
        self.top_scroll = Qt.QScrollArea()
        self.top_scroll.setFrameStyle(Qt.QFrame.NoFrame)
        self.top_scroll_layout.addWidget(self.top_scroll)
        self.top_scroll.setWidgetResizable(True)
        self.top_widget = Qt.QWidget()
        self.top_scroll.setWidget(self.top_widget)
        self.top_layout = Qt.QVBoxLayout(self.top_widget)
        self.top_grid_layout = Qt.QGridLayout()
        self.top_layout.addLayout(self.top_grid_layout)

        self.settings = Qt.QSettings("GNU Radio", "SpectroRadiometer")

        try:
            geometry = self.settings.value("geometry")
            if geometry:
                self.restoreGeometry(geometry)
        except BaseException as exc:
            print(f"Qt GUI: Could not restore geometry: {str(exc)}", file=sys.stderr)

        ##################################################
        # Parameters
        ##################################################
        self.abw = abw
        self.antenna = antenna
        self.baseline = baseline
        self.bbgain = bbgain
        self.clock = clock
        self.dcg = dcg
        self.decfile = decfile
        self.decln = decln
        self.device = device
        self.dfreq = dfreq
        self.fbsize = fbsize
        self.fftsize = fftsize
        self.frequency = frequency
        self.gain = gain
        self.ifgain = ifgain
        self.integration = integration
        self.latitude = latitude
        self.longitude = longitude
        self.mode = mode
        self.ppstime = ppstime
        self.prefix = prefix
        self.psrmode = psrmode
        self.ra = ra
        self.rfilist = rfilist
        self.spec_interval = spec_interval
        self.srate = srate
        self.tp_interval = tp_interval
        self.zerofile = zerofile
        self.zerotime = zerotime

        ##################################################
        # Variables
        ##################################################
        self.nphase = nphase = 2
        self.nchan = nchan = fftsize
        self.sinc_sample_locations = sinc_sample_locations = np.arange(-np.pi*4/2.0, np.pi*4/2.0, (np.pi/nchan)*(4/nphase))
        self.samp_rate = samp_rate = int(srate)
        self.ltp = ltp = time.gmtime(time.time())
        self.ifreq = ifreq = frequency
        self.wlam = wlam = 299792000.0/ifreq
        self.ui_decln = ui_decln = decln
        self.tp_pacer = tp_pacer = [-100.0]*fftsize
        self.sinc = sinc = np.sinc(sinc_sample_locations/np.pi)
        self.psrate = psrate = samp_rate/fftsize
        self.pchanwidth = pchanwidth = samp_rate/fbsize
        self.gmdate = gmdate = "%04d%02d%02d" % (ltp.tm_year, ltp.tm_mon, ltp.tm_mday)
        self.ebw = ebw = (samp_rate*0.8)/1.0e6
        self.win = win = fft.window.blackmanharris(fftsize)
        self.set_baseline = set_baseline = 0
        self.pparamstr = pparamstr = "%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (psrate/1e3, pchanwidth/1e3, ifreq/1.0e6,samp_rate/1.0e6,ebw,fbsize)
        self.pparam = pparam = prefix+"-"+gmdate+"-psr.params" if psrmode != 0 else "/dev/null"
        self.ira = ira = ra
        self.fstop = fstop = False
        self.frate = frate = (baseline/wlam)*7.3e-5*math.cos(math.radians(ui_decln))
        self.fft_probed = fft_probed = [-100.0]*fftsize
        self.fft_hz = fft_hz = 15
        self.fft_avg = fft_avg = integration
        self.fft2_probed = fft2_probed = [-100.0]*fftsize
        self.enable_normalize = enable_normalize = 0
        self.declination = declination = helper.get_decln(ui_decln,decfile,tp_pacer)
        self.dcgain = dcgain = dcg
        self.custom_window = custom_window = sinc*np.hamming(nphase*nchan)
        self.corr_probed = corr_probed = complex(0.0,0.0)
        self.clear_baseline = clear_baseline = 0
        self.annotation = annotation = ""
        self.ang = ang = 0
        self.wrstatus = wrstatus = open(pparam, "w").write(pparamstr)
        self.winsum = winsum = sum(map(lambda x:x*x, win))
        self.wchan = wchan = 0
        self.variable_qtgui_label_0 = variable_qtgui_label_0 = 'spectro_helper.lmst_string(time_pacer,longitude)'
        self.time_pacer = time_pacer = [-100.0]*fftsize
        self.start_km = start_km = helper.doppler_start(ifreq,dfreq,samp_rate)
        self.spec_labels = spec_labels = helper.get_spec_labels(mode)
        self.secondary_lmst_label = secondary_lmst_label = 'spectro_helper.lmst_string(time_pacer,longitude)'
        self.save_filter = save_filter = open("poopy.dat", "w").write(str(list(custom_window)))
        self.psrfilename = psrfilename = prefix+"-"+gmdate+"-psr.rfb8" if psrmode != 0 else "/dev/null"
        self.mode_map = mode_map = {"total" : "Continuum Power", "tp" : "Continuum Power", "diff" : "Differential/Added Power", "differential" : "Differential/Added Power", "correlator" : "Cross  Power", "interferometer": "Cross Power", "corr" : "Cross Power"}
        self.km_incr = km_incr = (((samp_rate/fftsize)/ifreq)*299792)*-1.0
        self.igain = igain = gain
        self.frotate = frotate = helper.fringe_stop (tp_pacer, ra, decln, longitude, latitude, baseline, fstop, ang, ifreq)
        self.fringe_label = fringe_label = (1.0/frate)
        self.fincr = fincr = (samp_rate/1.0e6)/fftsize
        self.fftrate = fftrate = float(samp_rate/fftsize)
        self.fft_log_status = fft_log_status = helper.fft_log(fft_probed,fft2_probed,corr_probed,ifreq,samp_rate,longitude,enable_normalize,prefix,declination,rfilist,dcgain,fft_avg,mode,zerotime,decfile,tp_interval,spec_interval,fft_hz)
        self.dcblock = dcblock = True
        self.curr_tp_vect = curr_tp_vect = helper.get_tp_vect(tp_pacer)
        self.curr_dx2 = curr_dx2 = helper.curr_diff(fft_probed,enable_normalize,fftsize,1)
        self.curr_dx = curr_dx = helper.curr_diff(fft_probed,enable_normalize,fftsize,0)
        self.clk_deriv = clk_deriv = 'None if clock in ["none", "default"] else clock'
        self.baseline_set_status = baseline_set_status = helper.baseline_setter(set_baseline)
        self.baseline_clear_status = baseline_clear_status = helper.baseline_clearer(clear_baseline)
        self.anno_status = anno_status = helper.do_annotation(ira,declination,baseline,annotation,srate*0.8,abw,ifreq,srate,prefix)
        self.actual_dec_label = actual_dec_label = helper.get_decln(ui_decln,decfile,tp_pacer)

        ##################################################
        # Blocks
        ##################################################

        self.main_tab = Qt.QTabWidget()
        self.main_tab_widget_0 = Qt.QWidget()
        self.main_tab_layout_0 = Qt.QBoxLayout(Qt.QBoxLayout.TopToBottom, self.main_tab_widget_0)
        self.main_tab_grid_layout_0 = Qt.QGridLayout()
        self.main_tab_layout_0.addLayout(self.main_tab_grid_layout_0)
        self.main_tab.addTab(self.main_tab_widget_0, 'Spectral')
        self.main_tab_widget_1 = Qt.QWidget()
        self.main_tab_layout_1 = Qt.QBoxLayout(Qt.QBoxLayout.TopToBottom, self.main_tab_widget_1)
        self.main_tab_grid_layout_1 = Qt.QGridLayout()
        self.main_tab_layout_1.addLayout(self.main_tab_grid_layout_1)
        self.main_tab.addTab(self.main_tab_widget_1, 'Continuum')
        self.top_layout.addWidget(self.main_tab)
        # Create the options list
        self._wchan_options = [0, 1]
        # Create the labels list
        self._wchan_labels = ['0', '1']
        # Create the combo box
        self._wchan_tool_bar = Qt.QToolBar(self)
        self._wchan_tool_bar.addWidget(Qt.QLabel("Waterfall Chan" + ": "))
        self._wchan_combo_box = Qt.QComboBox()
        self._wchan_tool_bar.addWidget(self._wchan_combo_box)
        for _label in self._wchan_labels: self._wchan_combo_box.addItem(_label)
        self._wchan_callback = lambda i: Qt.QMetaObject.invokeMethod(self._wchan_combo_box, "setCurrentIndex", Qt.Q_ARG("int", self._wchan_options.index(i)))
        self._wchan_callback(self.wchan)
        self._wchan_combo_box.currentIndexChanged.connect(
            lambda i: self.set_wchan(self._wchan_options[i]))
        # Create the radio buttons
        self.main_tab_grid_layout_0.addWidget(self._wchan_tool_bar, 2, 3, 1, 1)
        for r in range(2, 3):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(3, 4):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self.spec_tab = Qt.QTabWidget()
        self.spec_tab_widget_0 = Qt.QWidget()
        self.spec_tab_layout_0 = Qt.QBoxLayout(Qt.QBoxLayout.TopToBottom, self.spec_tab_widget_0)
        self.spec_tab_grid_layout_0 = Qt.QGridLayout()
        self.spec_tab_layout_0.addLayout(self.spec_tab_grid_layout_0)
        self.spec_tab.addTab(self.spec_tab_widget_0, 'Doppler')
        self.spec_tab_widget_1 = Qt.QWidget()
        self.spec_tab_layout_1 = Qt.QBoxLayout(Qt.QBoxLayout.TopToBottom, self.spec_tab_widget_1)
        self.spec_tab_grid_layout_1 = Qt.QGridLayout()
        self.spec_tab_layout_1.addLayout(self.spec_tab_grid_layout_1)
        self.spec_tab.addTab(self.spec_tab_widget_1, 'Frequency')
        self.spec_tab_widget_2 = Qt.QWidget()
        self.spec_tab_layout_2 = Qt.QBoxLayout(Qt.QBoxLayout.TopToBottom, self.spec_tab_widget_2)
        self.spec_tab_grid_layout_2 = Qt.QGridLayout()
        self.spec_tab_layout_2.addLayout(self.spec_tab_grid_layout_2)
        self.spec_tab.addTab(self.spec_tab_widget_2, 'Waterfall')
        self.main_tab_grid_layout_0.addWidget(self.spec_tab, 3, 0, 1, 4)
        for r in range(3, 4):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(0, 4):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self._igain_tool_bar = Qt.QToolBar(self)
        self._igain_tool_bar.addWidget(Qt.QLabel("RF Gain" + ": "))
        self._igain_line_edit = Qt.QLineEdit(str(self.igain))
        self._igain_tool_bar.addWidget(self._igain_line_edit)
        self._igain_line_edit.editingFinished.connect(
            lambda: self.set_igain(eng_notation.str_to_num(str(self._igain_line_edit.text()))))
        self.main_tab_grid_layout_0.addWidget(self._igain_tool_bar, 0, 3, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(3, 4):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self._ifreq_tool_bar = Qt.QToolBar(self)
        self._ifreq_tool_bar.addWidget(Qt.QLabel("Frequency" + ": "))
        self._ifreq_line_edit = Qt.QLineEdit(str(self.ifreq))
        self._ifreq_tool_bar.addWidget(self._ifreq_line_edit)
        self._ifreq_line_edit.editingFinished.connect(
            lambda: self.set_ifreq(eng_notation.str_to_num(str(self._ifreq_line_edit.text()))))
        self.main_tab_grid_layout_0.addWidget(self._ifreq_tool_bar, 0, 2, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(2, 3):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self.fft_probe = blocks.probe_signal_vf(fftsize)
        self.fft2_probe = blocks.probe_signal_vf(fftsize)
        _dcblock_check_box = Qt.QCheckBox("Enable DC block")
        self._dcblock_choices = {True: 1, False: 0}
        self._dcblock_choices_inv = dict((v,k) for k,v in self._dcblock_choices.items())
        self._dcblock_callback = lambda i: Qt.QMetaObject.invokeMethod(_dcblock_check_box, "setChecked", Qt.Q_ARG("bool", self._dcblock_choices_inv[i]))
        self._dcblock_callback(self.dcblock)
        _dcblock_check_box.stateChanged.connect(lambda i: self.set_dcblock(self._dcblock_choices[bool(i)]))
        self.main_tab_grid_layout_1.addWidget(_dcblock_check_box, 2, 0, 1, 1)
        for r in range(2, 3):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(0, 1):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        self.corr_probe = blocks.probe_signal_c()
        self._variable_qtgui_label_0_tool_bar = Qt.QToolBar(self)

        if None:
            self._variable_qtgui_label_0_formatter = None
        else:
            self._variable_qtgui_label_0_formatter = lambda x: str(x)

        self._variable_qtgui_label_0_tool_bar.addWidget(Qt.QLabel("Local Mean Sidereal Time"))
        self._variable_qtgui_label_0_label = Qt.QLabel(str(self._variable_qtgui_label_0_formatter(self.variable_qtgui_label_0)))
        self._variable_qtgui_label_0_tool_bar.addWidget(self._variable_qtgui_label_0_label)
        self.main_tab_grid_layout_0.addWidget(self._variable_qtgui_label_0_tool_bar, 1, 3, 1, 1)
        for r in range(1, 2):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(3, 4):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self._ui_decln_tool_bar = Qt.QToolBar(self)
        self._ui_decln_tool_bar.addWidget(Qt.QLabel("Declination" + ": "))
        self._ui_decln_line_edit = Qt.QLineEdit(str(self.ui_decln))
        self._ui_decln_tool_bar.addWidget(self._ui_decln_line_edit)
        self._ui_decln_line_edit.editingFinished.connect(
            lambda: self.set_ui_decln(eng_notation.str_to_num(str(self._ui_decln_line_edit.text()))))
        self.main_tab_grid_layout_0.addWidget(self._ui_decln_tool_bar, 1, 0, 1, 1)
        for r in range(1, 2):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(0, 1):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        def _tp_pacer_probe():
          while True:

            val = self.fft_probe.level()
            try:
              try:
                self.doc.add_next_tick_callback(functools.partial(self.set_tp_pacer,val))
              except AttributeError:
                self.set_tp_pacer(val)
            except AttributeError:
              pass
            time.sleep(1.0 / (1))
        _tp_pacer_thread = threading.Thread(target=_tp_pacer_probe)
        _tp_pacer_thread.daemon = True
        _tp_pacer_thread.start()
        def _time_pacer_probe():
          while True:

            val = self.fft_probe.level()
            try:
              try:
                self.doc.add_next_tick_callback(functools.partial(self.set_time_pacer,val))
              except AttributeError:
                self.set_time_pacer(val)
            except AttributeError:
              pass
            time.sleep(1.0 / (2))
        _time_pacer_thread = threading.Thread(target=_time_pacer_probe)
        _time_pacer_thread.daemon = True
        _time_pacer_thread.start()
        self.single_pole_iir_filter_xx_2 = filter.single_pole_iir_filter_cc((helper.getalpha(frate/2.0,fft_hz)), 1)
        self.single_pole_iir_filter_xx_1 = filter.single_pole_iir_filter_cc((helper.getalpha(fft_hz/2.0,samp_rate)), 1)
        self.single_pole_iir_filter_xx_0_0 = filter.single_pole_iir_filter_ff((helper.getalpha(fft_hz/2.0,fftrate)), fftsize)
        self.single_pole_iir_filter_xx_0 = filter.single_pole_iir_filter_ff((helper.getalpha(fft_hz/2.0,fftrate)), fftsize)
        _set_baseline_push_button = Qt.QPushButton('Set Baseline')
        _set_baseline_push_button = Qt.QPushButton('Set Baseline')
        self._set_baseline_choices = {'Pressed': 1, 'Released': 0}
        _set_baseline_push_button.pressed.connect(lambda: self.set_set_baseline(self._set_baseline_choices['Pressed']))
        _set_baseline_push_button.released.connect(lambda: self.set_set_baseline(self._set_baseline_choices['Released']))
        self.main_tab_grid_layout_0.addWidget(_set_baseline_push_button, 0, 0, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(0, 1):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self._secondary_lmst_label_tool_bar = Qt.QToolBar(self)

        if None:
            self._secondary_lmst_label_formatter = None
        else:
            self._secondary_lmst_label_formatter = lambda x: str(x)

        self._secondary_lmst_label_tool_bar.addWidget(Qt.QLabel("LMST"))
        self._secondary_lmst_label_label = Qt.QLabel(str(self._secondary_lmst_label_formatter(self.secondary_lmst_label)))
        self._secondary_lmst_label_tool_bar.addWidget(self._secondary_lmst_label_label)
        self.main_tab_grid_layout_1.addWidget(self._secondary_lmst_label_tool_bar, 0, 0, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(0, 1):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        self.qtgui_waterfall_sink_x_0 = qtgui.waterfall_sink_c(
            1024, #size
            window.WIN_BLACKMAN_hARRIS, #wintype
            ifreq, #fc
            samp_rate, #bw
            'Spectrogram', #name
            1, #number of inputs
            None # parent
        )
        self.qtgui_waterfall_sink_x_0.set_update_time(0.2)
        self.qtgui_waterfall_sink_x_0.enable_grid(False)
        self.qtgui_waterfall_sink_x_0.enable_axis_labels(True)



        labels = ['', '', '', '', '',
                  '', '', '', '', '']
        colors = [3, 0, 0, 0, 0,
                  0, 0, 0, 0, 0]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
                  1.0, 1.0, 1.0, 1.0, 1.0]

        for i in range(1):
            if len(labels[i]) == 0:
                self.qtgui_waterfall_sink_x_0.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_waterfall_sink_x_0.set_line_label(i, labels[i])
            self.qtgui_waterfall_sink_x_0.set_color_map(i, colors[i])
            self.qtgui_waterfall_sink_x_0.set_line_alpha(i, alphas[i])

        self.qtgui_waterfall_sink_x_0.set_intensity_range(-90, -40)

        self._qtgui_waterfall_sink_x_0_win = sip.wrapinstance(self.qtgui_waterfall_sink_x_0.qwidget(), Qt.QWidget)

        self.spec_tab_layout_2.addWidget(self._qtgui_waterfall_sink_x_0_win)
        self.qtgui_vector_sink_f_0_1 = qtgui.vector_sink_f(
            fftsize,
            ((ifreq-samp_rate/2)/1.0e6),
            fincr,
            "Frequency (MHz)",
            "Rel. Power (dB)",
            "Frequency (MHz)",
            2, # Number of inputs
            None # parent
        )
        self.qtgui_vector_sink_f_0_1.set_update_time((1.0/15))
        self.qtgui_vector_sink_f_0_1.set_y_axis((-1), (+5))
        self.qtgui_vector_sink_f_0_1.enable_autoscale(True)
        self.qtgui_vector_sink_f_0_1.enable_grid(True)
        self.qtgui_vector_sink_f_0_1.set_x_axis_units("MHz")
        self.qtgui_vector_sink_f_0_1.set_y_axis_units("dB")
        self.qtgui_vector_sink_f_0_1.set_ref_level(0)


        labels = [spec_labels[0], spec_labels[1], '', '', '',
            '', '', '', '', '']
        widths = [1, 1, 1, 1, 1,
            1, 1, 1, 1, 1]
        colors = ["blue", "red", "green", "black", "cyan",
            "magenta", "yellow", "dark red", "dark green", "dark blue"]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
            1.0, 1.0, 1.0, 1.0, 1.0]

        for i in range(2):
            if len(labels[i]) == 0:
                self.qtgui_vector_sink_f_0_1.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_vector_sink_f_0_1.set_line_label(i, labels[i])
            self.qtgui_vector_sink_f_0_1.set_line_width(i, widths[i])
            self.qtgui_vector_sink_f_0_1.set_line_color(i, colors[i])
            self.qtgui_vector_sink_f_0_1.set_line_alpha(i, alphas[i])

        self._qtgui_vector_sink_f_0_1_win = sip.wrapinstance(self.qtgui_vector_sink_f_0_1.qwidget(), Qt.QWidget)
        self.spec_tab_layout_1.addWidget(self._qtgui_vector_sink_f_0_1_win)
        self.qtgui_vector_sink_f_0_0 = qtgui.vector_sink_f(
            3600,
            0,
            (-(1.0/60.0)),
            "Time (Minutes)",
            "Deteced Power (arb units)",
            mode_map[mode],
            2, # Number of inputs
            None # parent
        )
        self.qtgui_vector_sink_f_0_0.set_update_time((1.0/5.0))
        self.qtgui_vector_sink_f_0_0.set_y_axis(0.0, 1.5)
        self.qtgui_vector_sink_f_0_0.enable_autoscale(False)
        self.qtgui_vector_sink_f_0_0.enable_grid(True)
        self.qtgui_vector_sink_f_0_0.set_x_axis_units("Mins")
        self.qtgui_vector_sink_f_0_0.set_y_axis_units("")
        self.qtgui_vector_sink_f_0_0.set_ref_level(0)


        labels = ['spectro_helper.plotlabel(mode,0)', 'spectro_helper.plotlabel(mode,1)', '', '', '',
            '', '', '', '', '']
        widths = [1, 1, 1, 1, 1,
            1, 1, 1, 1, 1]
        colors = ["blue", "red", "green", "black", "cyan",
            "magenta", "yellow", "dark red", "dark green", "dark blue"]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
            1.0, 1.0, 1.0, 1.0, 1.0]

        for i in range(2):
            if len(labels[i]) == 0:
                self.qtgui_vector_sink_f_0_0.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_vector_sink_f_0_0.set_line_label(i, labels[i])
            self.qtgui_vector_sink_f_0_0.set_line_width(i, widths[i])
            self.qtgui_vector_sink_f_0_0.set_line_color(i, colors[i])
            self.qtgui_vector_sink_f_0_0.set_line_alpha(i, alphas[i])

        self._qtgui_vector_sink_f_0_0_win = sip.wrapinstance(self.qtgui_vector_sink_f_0_0.qwidget(), Qt.QWidget)
        self.main_tab_grid_layout_1.addWidget(self._qtgui_vector_sink_f_0_0_win, 3, 0, 2, 4)
        for r in range(3, 5):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(0, 4):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        self.qtgui_vector_sink_f_0 = qtgui.vector_sink_f(
            fftsize,
            start_km,
            km_incr,
            "Doppler Velocity (km/s)",
            "Rel. Power (dB)",
            "Doppler Velocity",
            2, # Number of inputs
            None # parent
        )
        self.qtgui_vector_sink_f_0.set_update_time((1.0/15))
        self.qtgui_vector_sink_f_0.set_y_axis((-1), (+5))
        self.qtgui_vector_sink_f_0.enable_autoscale(True)
        self.qtgui_vector_sink_f_0.enable_grid(True)
        self.qtgui_vector_sink_f_0.set_x_axis_units("km/s")
        self.qtgui_vector_sink_f_0.set_y_axis_units("dB")
        self.qtgui_vector_sink_f_0.set_ref_level(0)


        labels = [spec_labels[0], spec_labels[1], '', '', '',
            '', '', '', '', '']
        widths = [1, 1, 1, 1, 1,
            1, 1, 1, 1, 1]
        colors = ["blue", "red", "green", "black", "cyan",
            "magenta", "yellow", "dark red", "dark green", "dark blue"]
        alphas = [1.0, 1.0, 1.0, 1.0, 1.0,
            1.0, 1.0, 1.0, 1.0, 1.0]

        for i in range(2):
            if len(labels[i]) == 0:
                self.qtgui_vector_sink_f_0.set_line_label(i, "Data {0}".format(i))
            else:
                self.qtgui_vector_sink_f_0.set_line_label(i, labels[i])
            self.qtgui_vector_sink_f_0.set_line_width(i, widths[i])
            self.qtgui_vector_sink_f_0.set_line_color(i, colors[i])
            self.qtgui_vector_sink_f_0.set_line_alpha(i, alphas[i])

        self._qtgui_vector_sink_f_0_win = sip.wrapinstance(self.qtgui_vector_sink_f_0.qwidget(), Qt.QWidget)
        self.spec_tab_layout_0.addWidget(self._qtgui_vector_sink_f_0_win)
        self.osmosdr_source_0 = osmosdr.source(
            args="numchan=" + str(2) + " " + device
        )
        self.osmosdr_source_0.set_time_unknown_pps(osmosdr.time_spec_t())
        self.osmosdr_source_0.set_sample_rate(samp_rate)
        self.osmosdr_source_0.set_center_freq(ifreq, 0)
        self.osmosdr_source_0.set_freq_corr(0, 0)
        self.osmosdr_source_0.set_dc_offset_mode(2, 0)
        self.osmosdr_source_0.set_iq_balance_mode(0, 0)
        self.osmosdr_source_0.set_gain_mode(False, 0)
        self.osmosdr_source_0.set_gain(igain, 0)
        self.osmosdr_source_0.set_if_gain(ifgain, 0)
        self.osmosdr_source_0.set_bb_gain(bbgain, 0)
        self.osmosdr_source_0.set_antenna(antenna, 0)
        self.osmosdr_source_0.set_bandwidth(abw, 0)
        self.osmosdr_source_0.set_center_freq(ifreq, 1)
        self.osmosdr_source_0.set_freq_corr(0, 1)
        self.osmosdr_source_0.set_dc_offset_mode(2, 1)
        self.osmosdr_source_0.set_iq_balance_mode(0, 1)
        self.osmosdr_source_0.set_gain_mode(False, 1)
        self.osmosdr_source_0.set_gain(igain , 1)
        self.osmosdr_source_0.set_if_gain(ifgain, 1)
        self.osmosdr_source_0.set_bb_gain(bbgain, 1)
        self.osmosdr_source_0.set_antenna(antenna, 1)
        self.osmosdr_source_0.set_bandwidth(abw, 1)
        self._ira_tool_bar = Qt.QToolBar(self)
        self._ira_tool_bar.addWidget(Qt.QLabel("Target Right Ascension" + ": "))
        self._ira_line_edit = Qt.QLineEdit(str(self.ira))
        self._ira_tool_bar.addWidget(self._ira_line_edit)
        self._ira_line_edit.editingFinished.connect(
            lambda: self.set_ira(eng_notation.str_to_num(str(self._ira_line_edit.text()))))
        self.main_tab_grid_layout_0.addWidget(self._ira_tool_bar, 2, 0, 1, 1)
        for r in range(2, 3):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(0, 1):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        _fstop_check_box = Qt.QCheckBox("Fringe Stop")
        self._fstop_choices = {True: True, False: False}
        self._fstop_choices_inv = dict((v,k) for k,v in self._fstop_choices.items())
        self._fstop_callback = lambda i: Qt.QMetaObject.invokeMethod(_fstop_check_box, "setChecked", Qt.Q_ARG("bool", self._fstop_choices_inv[i]))
        self._fstop_callback(self.fstop)
        _fstop_check_box.stateChanged.connect(lambda i: self.set_fstop(self._fstop_choices[bool(i)]))
        self.main_tab_grid_layout_1.addWidget(_fstop_check_box, 2, 1, 1, 1)
        for r in range(2, 3):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(1, 2):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        self._fringe_label_tool_bar = Qt.QToolBar(self)

        if None:
            self._fringe_label_formatter = None
        else:
            self._fringe_label_formatter = lambda x: eng_notation.num_to_str(x)

        self._fringe_label_tool_bar.addWidget(Qt.QLabel("Fringe Period(secs)"))
        self._fringe_label_label = Qt.QLabel(str(self._fringe_label_formatter(self.fringe_label)))
        self._fringe_label_tool_bar.addWidget(self._fringe_label_label)
        self.main_tab_grid_layout_1.addWidget(self._fringe_label_tool_bar, 0, 1, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(1, 2):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        self.fft_vxx_0_0 = fft.fft_vcc(fftsize, True, [], True, 1)
        self.fft_vxx_0 = fft.fft_vcc(fftsize, True, [], True, 1)
        def _fft_probed_probe():
          while True:

            val = self.fft_probe.level()
            try:
              try:
                self.doc.add_next_tick_callback(functools.partial(self.set_fft_probed,val))
              except AttributeError:
                self.set_fft_probed(val)
            except AttributeError:
              pass
            time.sleep(1.0 / (fft_hz))
        _fft_probed_thread = threading.Thread(target=_fft_probed_probe)
        _fft_probed_thread.daemon = True
        _fft_probed_thread.start()
        self._fft_avg_range = qtgui.Range(0.5, 300, 0.5, integration, 200)
        self._fft_avg_win = qtgui.RangeWidget(self._fft_avg_range, self.set_fft_avg, "Int. Time (Sec.)", "counter", float, QtCore.Qt.Horizontal)
        self.main_tab_grid_layout_0.addWidget(self._fft_avg_win, 1, 2, 1, 1)
        for r in range(1, 2):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(2, 3):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        def _fft2_probed_probe():
          while True:

            val = self.fft2_probe.level()
            try:
              try:
                self.doc.add_next_tick_callback(functools.partial(self.set_fft2_probed,val))
              except AttributeError:
                self.set_fft2_probed(val)
            except AttributeError:
              pass
            time.sleep(1.0 / (fft_hz))
        _fft2_probed_thread = threading.Thread(target=_fft2_probed_probe)
        _fft2_probed_thread.daemon = True
        _fft2_probed_thread.start()
        # Create the options list
        self._dcgain_options = [100, 1000, 10000, 100000, 1000000]
        # Create the labels list
        self._dcgain_labels = ['1e2', '1e3', '1e4', '1e5', '1e6']
        # Create the combo box
        # Create the radio buttons
        self._dcgain_group_box = Qt.QGroupBox("Detector Gain" + ": ")
        self._dcgain_box = Qt.QHBoxLayout()
        class variable_chooser_button_group(Qt.QButtonGroup):
            def __init__(self, parent=None):
                Qt.QButtonGroup.__init__(self, parent)
            @pyqtSlot(int)
            def updateButtonChecked(self, button_id):
                self.button(button_id).setChecked(True)
        self._dcgain_button_group = variable_chooser_button_group()
        self._dcgain_group_box.setLayout(self._dcgain_box)
        for i, _label in enumerate(self._dcgain_labels):
            radio_button = Qt.QRadioButton(_label)
            self._dcgain_box.addWidget(radio_button)
            self._dcgain_button_group.addButton(radio_button, i)
        self._dcgain_callback = lambda i: Qt.QMetaObject.invokeMethod(self._dcgain_button_group, "updateButtonChecked", Qt.Q_ARG("int", self._dcgain_options.index(i)))
        self._dcgain_callback(self.dcgain)
        self._dcgain_button_group.buttonClicked[int].connect(
            lambda i: self.set_dcgain(self._dcgain_options[i]))
        self.main_tab_grid_layout_1.addWidget(self._dcgain_group_box, 0, 2, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(2, 3):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        def _corr_probed_probe():
          while True:

            val = self.corr_probe.level()
            try:
              try:
                self.doc.add_next_tick_callback(functools.partial(self.set_corr_probed,val))
              except AttributeError:
                self.set_corr_probed(val)
            except AttributeError:
              pass
            time.sleep(1.0 / (fft_hz))
        _corr_probed_thread = threading.Thread(target=_corr_probed_probe)
        _corr_probed_thread.daemon = True
        _corr_probed_thread.start()
        _clear_baseline_push_button = Qt.QPushButton('Clear Baseline')
        _clear_baseline_push_button = Qt.QPushButton('Clear Baseline')
        self._clear_baseline_choices = {'Pressed': 1, 'Released': 0}
        _clear_baseline_push_button.pressed.connect(lambda: self.set_clear_baseline(self._clear_baseline_choices['Pressed']))
        _clear_baseline_push_button.released.connect(lambda: self.set_clear_baseline(self._clear_baseline_choices['Released']))
        self.main_tab_grid_layout_0.addWidget(_clear_baseline_push_button, 0, 1, 1, 1)
        for r in range(0, 1):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(1, 2):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self.blocks_sub_xx_0 = blocks.sub_cc(1)
        self.blocks_stream_to_vector_0_0 = blocks.stream_to_vector(gr.sizeof_gr_complex*1, fftsize)
        self.blocks_stream_to_vector_0 = blocks.stream_to_vector(gr.sizeof_gr_complex*1, fftsize)
        self.blocks_null_source_0 = blocks.null_source(gr.sizeof_float*3600)
        self.blocks_nlog10_ff_0_0 = blocks.nlog10_ff(10, fftsize, (-20*math.log10(fftsize)-10.0*math.log10(winsum/fftsize)-20*math.log10(1)))
        self.blocks_nlog10_ff_0 = blocks.nlog10_ff(10, fftsize, (-20*math.log10(fftsize)-10.0*math.log10(winsum/fftsize)-20*math.log10(1)))
        self.blocks_multiply_const_vxx_4_2 = blocks.multiply_const_vcc(custom_window[0:nchan])
        self.blocks_multiply_const_vxx_4_0_0 = blocks.multiply_const_vcc(custom_window[-nchan:])
        self.blocks_multiply_const_vxx_4_0 = blocks.multiply_const_vcc(custom_window[-nchan:])
        self.blocks_multiply_const_vxx_4 = blocks.multiply_const_vcc(custom_window[0:nchan])
        self.blocks_multiply_const_vxx_3_0 = blocks.multiply_const_cc(1.0  if wchan == 1 else 0.0)
        self.blocks_multiply_const_vxx_3 = blocks.multiply_const_cc(1.0 if wchan == 0 else 0)
        self.blocks_multiply_const_vxx_2 = blocks.multiply_const_cc(dcblock)
        self.blocks_multiply_const_vxx_1 = blocks.multiply_const_vff([0.0]*fftsize)
        self.blocks_multiply_const_vxx_0 = blocks.multiply_const_cc(frotate)
        self.blocks_multiply_conjugate_cc_0 = blocks.multiply_conjugate_cc(1)
        self.blocks_keep_one_in_n_1 = blocks.keep_one_in_n(gr.sizeof_gr_complex*1, (int(samp_rate/fft_hz)))
        self.blocks_keep_one_in_n_0_0 = blocks.keep_one_in_n(gr.sizeof_float*fftsize, (int((samp_rate/fftsize)/50)))
        self.blocks_keep_one_in_n_0 = blocks.keep_one_in_n(gr.sizeof_float*fftsize, (int((samp_rate/fftsize)/50)))
        self.blocks_keep_m_in_n_0_0 = blocks.keep_m_in_n(gr.sizeof_gr_complex, (2*fftsize), (3*fftsize), 0)
        self.blocks_keep_m_in_n_0 = blocks.keep_m_in_n(gr.sizeof_gr_complex, (2*fftsize), (3*fftsize), 0)
        self.blocks_delay_0_1 = blocks.delay(gr.sizeof_gr_complex*fftsize, 1)
        self.blocks_delay_0 = blocks.delay(gr.sizeof_gr_complex*fftsize, 1)
        self.blocks_complex_to_mag_squared_0_0 = blocks.complex_to_mag_squared(fftsize)
        self.blocks_complex_to_mag_squared_0 = blocks.complex_to_mag_squared(fftsize)
        self.blocks_add_xx_1_0 = blocks.add_vcc(fftsize)
        self.blocks_add_xx_1 = blocks.add_vcc(fftsize)
        self.blocks_add_xx_0 = blocks.add_vcc(1)
        self.blocks_add_const_vxx_1 = blocks.add_const_cc(1.0e-14)
        self.blocks_add_const_vxx_0_1 = blocks.add_const_vff(curr_dx2)
        self.blocks_add_const_vxx_0_0_0 = blocks.add_const_vff(curr_tp_vect[1])
        self.blocks_add_const_vxx_0_0 = blocks.add_const_vff(curr_tp_vect[0])
        self.blocks_add_const_vxx_0 = blocks.add_const_vff(curr_dx)
        self._annotation_tool_bar = Qt.QToolBar(self)
        self._annotation_tool_bar.addWidget(Qt.QLabel("Quick Annotation" + ": "))
        self._annotation_line_edit = Qt.QLineEdit(str(self.annotation))
        self._annotation_tool_bar.addWidget(self._annotation_line_edit)
        self._annotation_line_edit.editingFinished.connect(
            lambda: self.set_annotation(str(str(self._annotation_line_edit.text()))))
        self.main_tab_grid_layout_0.addWidget(self._annotation_tool_bar, 2, 1, 1, 2)
        for r in range(2, 3):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(1, 3):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)
        self._ang_range = qtgui.Range(-180, 180, 2, 0, 200)
        self._ang_win = qtgui.RangeWidget(self._ang_range, self.set_ang, "Phase Angle Adjust", "slider", float, QtCore.Qt.Horizontal)
        self.main_tab_grid_layout_1.addWidget(self._ang_win, 1, 0, 1, 3)
        for r in range(1, 2):
            self.main_tab_grid_layout_1.setRowStretch(r, 1)
        for c in range(0, 3):
            self.main_tab_grid_layout_1.setColumnStretch(c, 1)
        self._actual_dec_label_tool_bar = Qt.QToolBar(self)

        if None:
            self._actual_dec_label_formatter = None
        else:
            self._actual_dec_label_formatter = lambda x: eng_notation.num_to_str(x)

        self._actual_dec_label_tool_bar.addWidget(Qt.QLabel("Actual DEC"))
        self._actual_dec_label_label = Qt.QLabel(str(self._actual_dec_label_formatter(self.actual_dec_label)))
        self._actual_dec_label_tool_bar.addWidget(self._actual_dec_label_label)
        self.main_tab_grid_layout_0.addWidget(self._actual_dec_label_tool_bar, 1, 1, 1, 1)
        for r in range(1, 2):
            self.main_tab_grid_layout_0.setRowStretch(r, 1)
        for c in range(1, 2):
            self.main_tab_grid_layout_0.setColumnStretch(c, 1)


        ##################################################
        # Connections
        ##################################################
        self.connect((self.blocks_add_const_vxx_0, 0), (self.qtgui_vector_sink_f_0, 0))
        self.connect((self.blocks_add_const_vxx_0, 0), (self.qtgui_vector_sink_f_0_1, 0))
        self.connect((self.blocks_add_const_vxx_0_0, 0), (self.qtgui_vector_sink_f_0_0, 0))
        self.connect((self.blocks_add_const_vxx_0_0_0, 0), (self.qtgui_vector_sink_f_0_0, 1))
        self.connect((self.blocks_add_const_vxx_0_1, 0), (self.qtgui_vector_sink_f_0, 1))
        self.connect((self.blocks_add_const_vxx_0_1, 0), (self.qtgui_vector_sink_f_0_1, 1))
        self.connect((self.blocks_add_const_vxx_1, 0), (self.blocks_stream_to_vector_0_0, 0))
        self.connect((self.blocks_add_xx_0, 0), (self.qtgui_waterfall_sink_x_0, 0))
        self.connect((self.blocks_add_xx_1, 0), (self.fft_vxx_0, 0))
        self.connect((self.blocks_add_xx_1_0, 0), (self.fft_vxx_0_0, 0))
        self.connect((self.blocks_complex_to_mag_squared_0, 0), (self.single_pole_iir_filter_xx_0, 0))
        self.connect((self.blocks_complex_to_mag_squared_0_0, 0), (self.single_pole_iir_filter_xx_0_0, 0))
        self.connect((self.blocks_delay_0, 0), (self.blocks_multiply_const_vxx_4, 0))
        self.connect((self.blocks_delay_0_1, 0), (self.blocks_multiply_const_vxx_4_2, 0))
        self.connect((self.blocks_keep_m_in_n_0, 0), (self.blocks_stream_to_vector_0, 0))
        self.connect((self.blocks_keep_m_in_n_0_0, 0), (self.blocks_add_const_vxx_1, 0))
        self.connect((self.blocks_keep_one_in_n_0, 0), (self.blocks_nlog10_ff_0, 0))
        self.connect((self.blocks_keep_one_in_n_0_0, 0), (self.blocks_nlog10_ff_0_0, 0))
        self.connect((self.blocks_keep_one_in_n_1, 0), (self.blocks_sub_xx_0, 0))
        self.connect((self.blocks_keep_one_in_n_1, 0), (self.single_pole_iir_filter_xx_2, 0))
        self.connect((self.blocks_multiply_conjugate_cc_0, 0), (self.single_pole_iir_filter_xx_1, 0))
        self.connect((self.blocks_multiply_const_vxx_0, 0), (self.blocks_multiply_conjugate_cc_0, 0))
        self.connect((self.blocks_multiply_const_vxx_1, 0), (self.blocks_add_const_vxx_0, 0))
        self.connect((self.blocks_multiply_const_vxx_1, 0), (self.blocks_add_const_vxx_0_1, 0))
        self.connect((self.blocks_multiply_const_vxx_2, 0), (self.blocks_sub_xx_0, 1))
        self.connect((self.blocks_multiply_const_vxx_3, 0), (self.blocks_add_xx_0, 0))
        self.connect((self.blocks_multiply_const_vxx_3_0, 0), (self.blocks_add_xx_0, 1))
        self.connect((self.blocks_multiply_const_vxx_4, 0), (self.blocks_add_xx_1, 1))
        self.connect((self.blocks_multiply_const_vxx_4_0, 0), (self.blocks_add_xx_1, 0))
        self.connect((self.blocks_multiply_const_vxx_4_0_0, 0), (self.blocks_add_xx_1_0, 0))
        self.connect((self.blocks_multiply_const_vxx_4_2, 0), (self.blocks_add_xx_1_0, 1))
        self.connect((self.blocks_nlog10_ff_0, 0), (self.blocks_multiply_const_vxx_1, 0))
        self.connect((self.blocks_nlog10_ff_0, 0), (self.fft_probe, 0))
        self.connect((self.blocks_nlog10_ff_0_0, 0), (self.fft2_probe, 0))
        self.connect((self.blocks_null_source_0, 0), (self.blocks_add_const_vxx_0_0, 0))
        self.connect((self.blocks_null_source_0, 0), (self.blocks_add_const_vxx_0_0_0, 0))
        self.connect((self.blocks_stream_to_vector_0, 0), (self.blocks_delay_0, 0))
        self.connect((self.blocks_stream_to_vector_0, 0), (self.blocks_multiply_const_vxx_4_0, 0))
        self.connect((self.blocks_stream_to_vector_0_0, 0), (self.blocks_delay_0_1, 0))
        self.connect((self.blocks_stream_to_vector_0_0, 0), (self.blocks_multiply_const_vxx_4_0_0, 0))
        self.connect((self.blocks_sub_xx_0, 0), (self.corr_probe, 0))
        self.connect((self.fft_vxx_0, 0), (self.blocks_complex_to_mag_squared_0, 0))
        self.connect((self.fft_vxx_0_0, 0), (self.blocks_complex_to_mag_squared_0_0, 0))
        self.connect((self.osmosdr_source_0, 0), (self.blocks_keep_m_in_n_0, 0))
        self.connect((self.osmosdr_source_0, 1), (self.blocks_keep_m_in_n_0_0, 0))
        self.connect((self.osmosdr_source_0, 1), (self.blocks_multiply_conjugate_cc_0, 1))
        self.connect((self.osmosdr_source_0, 0), (self.blocks_multiply_const_vxx_0, 0))
        self.connect((self.osmosdr_source_0, 0), (self.blocks_multiply_const_vxx_3, 0))
        self.connect((self.osmosdr_source_0, 1), (self.blocks_multiply_const_vxx_3_0, 0))
        self.connect((self.single_pole_iir_filter_xx_0, 0), (self.blocks_keep_one_in_n_0, 0))
        self.connect((self.single_pole_iir_filter_xx_0_0, 0), (self.blocks_keep_one_in_n_0_0, 0))
        self.connect((self.single_pole_iir_filter_xx_1, 0), (self.blocks_keep_one_in_n_1, 0))
        self.connect((self.single_pole_iir_filter_xx_2, 0), (self.blocks_multiply_const_vxx_2, 0))


    def closeEvent(self, event):
        self.settings = Qt.QSettings("GNU Radio", "SpectroRadiometer")
        self.settings.setValue("geometry", self.saveGeometry())
        self.stop()
        self.wait()

        event.accept()

    def get_abw(self):
        return self.abw

    def set_abw(self, abw):
        self.abw = abw
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        self.osmosdr_source_0.set_bandwidth(self.abw, 0)
        self.osmosdr_source_0.set_bandwidth(self.abw, 1)

    def get_antenna(self):
        return self.antenna

    def set_antenna(self, antenna):
        self.antenna = antenna
        self.osmosdr_source_0.set_antenna(self.antenna, 0)
        self.osmosdr_source_0.set_antenna(self.antenna, 1)

    def get_baseline(self):
        return self.baseline

    def set_baseline(self, baseline):
        self.baseline = baseline
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        self.set_frate((self.baseline/self.wlam)*7.3e-5*math.cos(math.radians(self.ui_decln)))
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))

    def get_bbgain(self):
        return self.bbgain

    def set_bbgain(self, bbgain):
        self.bbgain = bbgain
        self.osmosdr_source_0.set_bb_gain(self.bbgain, 0)
        self.osmosdr_source_0.set_bb_gain(self.bbgain, 1)

    def get_clock(self):
        return self.clock

    def set_clock(self, clock):
        self.clock = clock

    def get_dcg(self):
        return self.dcg

    def set_dcg(self, dcg):
        self.dcg = dcg
        self.set_dcgain(self.dcg)

    def get_decfile(self):
        return self.decfile

    def set_decfile(self, decfile):
        self.decfile = decfile
        self.set_actual_dec_label(helper.get_decln(self.ui_decln,self.decfile,self.tp_pacer))
        self.set_declination(helper.get_decln(self.ui_decln,self.decfile,self.tp_pacer))
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_decln(self):
        return self.decln

    def set_decln(self, decln):
        self.decln = decln
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))
        self.set_ui_decln(self.decln)

    def get_device(self):
        return self.device

    def set_device(self, device):
        self.device = device

    def get_dfreq(self):
        return self.dfreq

    def set_dfreq(self, dfreq):
        self.dfreq = dfreq
        self.set_start_km(helper.doppler_start(self.ifreq,self.dfreq,self.samp_rate))

    def get_fbsize(self):
        return self.fbsize

    def set_fbsize(self, fbsize):
        self.fbsize = fbsize
        self.set_pchanwidth(self.samp_rate/self.fbsize)
        self.set_pparamstr("%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (self.psrate/1e3, self.pchanwidth/1e3, self.ifreq/1.0e6,self.samp_rate/1.0e6,self.ebw,self.fbsize))

    def get_fftsize(self):
        return self.fftsize

    def set_fftsize(self, fftsize):
        self.fftsize = fftsize
        self.set_curr_dx(helper.curr_diff(self.fft_probed,self.enable_normalize,self.fftsize,0))
        self.set_curr_dx2(helper.curr_diff(self.fft_probed,self.enable_normalize,self.fftsize,1))
        self.set_fft2_probed([-100.0]*self.fftsize)
        self.set_fft_probed([-100.0]*self.fftsize)
        self.set_fftrate(float(self.samp_rate/self.fftsize))
        self.set_fincr((self.samp_rate/1.0e6)/self.fftsize)
        self.set_km_incr((((self.samp_rate/self.fftsize)/self.ifreq)*299792)*-1.0)
        self.set_nchan(self.fftsize)
        self.set_psrate(self.samp_rate/self.fftsize)
        self.set_time_pacer([-100.0]*self.fftsize)
        self.set_tp_pacer([-100.0]*self.fftsize)
        self.set_win(fft.window.blackmanharris(self.fftsize))
        self.blocks_keep_m_in_n_0.set_m((2*self.fftsize))
        self.blocks_keep_m_in_n_0.set_n((3*self.fftsize))
        self.blocks_keep_m_in_n_0_0.set_m((2*self.fftsize))
        self.blocks_keep_m_in_n_0_0.set_n((3*self.fftsize))
        self.blocks_keep_one_in_n_0.set_n((int((self.samp_rate/self.fftsize)/50)))
        self.blocks_keep_one_in_n_0_0.set_n((int((self.samp_rate/self.fftsize)/50)))
        self.blocks_multiply_const_vxx_1.set_k([0.0]*self.fftsize)

    def get_frequency(self):
        return self.frequency

    def set_frequency(self, frequency):
        self.frequency = frequency
        self.set_ifreq(self.frequency)

    def get_gain(self):
        return self.gain

    def set_gain(self, gain):
        self.gain = gain
        self.set_igain(self.gain)

    def get_ifgain(self):
        return self.ifgain

    def set_ifgain(self, ifgain):
        self.ifgain = ifgain
        self.osmosdr_source_0.set_if_gain(self.ifgain, 0)
        self.osmosdr_source_0.set_if_gain(self.ifgain, 1)

    def get_integration(self):
        return self.integration

    def set_integration(self, integration):
        self.integration = integration
        self.set_fft_avg(self.integration)

    def get_latitude(self):
        return self.latitude

    def set_latitude(self, latitude):
        self.latitude = latitude
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))

    def get_longitude(self):
        return self.longitude

    def set_longitude(self, longitude):
        self.longitude = longitude
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))

    def get_mode(self):
        return self.mode

    def set_mode(self, mode):
        self.mode = mode
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))
        self.set_spec_labels(helper.get_spec_labels(self.mode))

    def get_ppstime(self):
        return self.ppstime

    def set_ppstime(self, ppstime):
        self.ppstime = ppstime

    def get_prefix(self):
        return self.prefix

    def set_prefix(self, prefix):
        self.prefix = prefix
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))
        self.set_pparam(self.prefix+"-"+self.gmdate+"-psr.params" if self.psrmode != 0 else "/dev/null")
        self.set_psrfilename(self.prefix+"-"+self.gmdate+"-psr.rfb8" if self.psrmode != 0 else "/dev/null")

    def get_psrmode(self):
        return self.psrmode

    def set_psrmode(self, psrmode):
        self.psrmode = psrmode
        self.set_pparam(self.prefix+"-"+self.gmdate+"-psr.params" if self.psrmode != 0 else "/dev/null")
        self.set_psrfilename(self.prefix+"-"+self.gmdate+"-psr.rfb8" if self.psrmode != 0 else "/dev/null")

    def get_ra(self):
        return self.ra

    def set_ra(self, ra):
        self.ra = ra
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))
        self.set_ira(self.ra)

    def get_rfilist(self):
        return self.rfilist

    def set_rfilist(self, rfilist):
        self.rfilist = rfilist
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_spec_interval(self):
        return self.spec_interval

    def set_spec_interval(self, spec_interval):
        self.spec_interval = spec_interval
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_srate(self):
        return self.srate

    def set_srate(self, srate):
        self.srate = srate
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        self.set_samp_rate(int(self.srate))

    def get_tp_interval(self):
        return self.tp_interval

    def set_tp_interval(self, tp_interval):
        self.tp_interval = tp_interval
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_zerofile(self):
        return self.zerofile

    def set_zerofile(self, zerofile):
        self.zerofile = zerofile

    def get_zerotime(self):
        return self.zerotime

    def set_zerotime(self, zerotime):
        self.zerotime = zerotime
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_nphase(self):
        return self.nphase

    def set_nphase(self, nphase):
        self.nphase = nphase
        self.set_custom_window(self.sinc*np.hamming(self.nphase*self.nchan))
        self.set_sinc_sample_locations(np.arange(-np.pi*4/2.0, np.pi*4/2.0, (np.pi/self.nchan)*(4/self.nphase)))

    def get_nchan(self):
        return self.nchan

    def set_nchan(self, nchan):
        self.nchan = nchan
        self.set_custom_window(self.sinc*np.hamming(self.nphase*self.nchan))
        self.set_sinc_sample_locations(np.arange(-np.pi*4/2.0, np.pi*4/2.0, (np.pi/self.nchan)*(4/self.nphase)))
        self.blocks_multiply_const_vxx_4.set_k(self.custom_window[0:self.nchan])
        self.blocks_multiply_const_vxx_4_0.set_k(self.custom_window[-self.nchan:])
        self.blocks_multiply_const_vxx_4_0_0.set_k(self.custom_window[-self.nchan:])
        self.blocks_multiply_const_vxx_4_2.set_k(self.custom_window[0:self.nchan])

    def get_sinc_sample_locations(self):
        return self.sinc_sample_locations

    def set_sinc_sample_locations(self, sinc_sample_locations):
        self.sinc_sample_locations = sinc_sample_locations
        self.set_sinc(np.sinc(self.sinc_sample_locations/np.pi))

    def get_samp_rate(self):
        return self.samp_rate

    def set_samp_rate(self, samp_rate):
        self.samp_rate = samp_rate
        self.set_ebw((self.samp_rate*0.8)/1.0e6)
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))
        self.set_fftrate(float(self.samp_rate/self.fftsize))
        self.set_fincr((self.samp_rate/1.0e6)/self.fftsize)
        self.set_km_incr((((self.samp_rate/self.fftsize)/self.ifreq)*299792)*-1.0)
        self.set_pchanwidth(self.samp_rate/self.fbsize)
        self.set_pparamstr("%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (self.psrate/1e3, self.pchanwidth/1e3, self.ifreq/1.0e6,self.samp_rate/1.0e6,self.ebw,self.fbsize))
        self.set_psrate(self.samp_rate/self.fftsize)
        self.set_start_km(helper.doppler_start(self.ifreq,self.dfreq,self.samp_rate))
        self.blocks_keep_one_in_n_0.set_n((int((self.samp_rate/self.fftsize)/50)))
        self.blocks_keep_one_in_n_0_0.set_n((int((self.samp_rate/self.fftsize)/50)))
        self.blocks_keep_one_in_n_1.set_n((int(self.samp_rate/self.fft_hz)))
        self.osmosdr_source_0.set_sample_rate(self.samp_rate)
        self.qtgui_vector_sink_f_0_1.set_x_axis(((self.ifreq-self.samp_rate/2)/1.0e6), self.fincr)
        self.qtgui_waterfall_sink_x_0.set_frequency_range(self.ifreq, self.samp_rate)
        self.single_pole_iir_filter_xx_1.set_taps((helper.getalpha(self.fft_hz/2.0,self.samp_rate)))

    def get_ltp(self):
        return self.ltp

    def set_ltp(self, ltp):
        self.ltp = ltp

    def get_ifreq(self):
        return self.ifreq

    def set_ifreq(self, ifreq):
        self.ifreq = ifreq
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))
        Qt.QMetaObject.invokeMethod(self._ifreq_line_edit, "setText", Qt.Q_ARG("QString", eng_notation.num_to_str(self.ifreq)))
        self.set_km_incr((((self.samp_rate/self.fftsize)/self.ifreq)*299792)*-1.0)
        self.set_pparamstr("%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (self.psrate/1e3, self.pchanwidth/1e3, self.ifreq/1.0e6,self.samp_rate/1.0e6,self.ebw,self.fbsize))
        self.set_start_km(helper.doppler_start(self.ifreq,self.dfreq,self.samp_rate))
        self.set_wlam(299792000.0/self.ifreq)
        self.osmosdr_source_0.set_center_freq(self.ifreq, 0)
        self.osmosdr_source_0.set_center_freq(self.ifreq, 1)
        self.qtgui_vector_sink_f_0_1.set_x_axis(((self.ifreq-self.samp_rate/2)/1.0e6), self.fincr)
        self.qtgui_waterfall_sink_x_0.set_frequency_range(self.ifreq, self.samp_rate)

    def get_wlam(self):
        return self.wlam

    def set_wlam(self, wlam):
        self.wlam = wlam
        self.set_frate((self.baseline/self.wlam)*7.3e-5*math.cos(math.radians(self.ui_decln)))

    def get_ui_decln(self):
        return self.ui_decln

    def set_ui_decln(self, ui_decln):
        self.ui_decln = ui_decln
        self.set_actual_dec_label(helper.get_decln(self.ui_decln,self.decfile,self.tp_pacer))
        self.set_declination(helper.get_decln(self.ui_decln,self.decfile,self.tp_pacer))
        self.set_frate((self.baseline/self.wlam)*7.3e-5*math.cos(math.radians(self.ui_decln)))
        Qt.QMetaObject.invokeMethod(self._ui_decln_line_edit, "setText", Qt.Q_ARG("QString", eng_notation.num_to_str(self.ui_decln)))

    def get_tp_pacer(self):
        return self.tp_pacer

    def set_tp_pacer(self, tp_pacer):
        self.tp_pacer = tp_pacer
        self.set_actual_dec_label(helper.get_decln(self.ui_decln,self.decfile,self.tp_pacer))
        self.set_curr_tp_vect(helper.get_tp_vect(self.tp_pacer))
        self.set_declination(helper.get_decln(self.ui_decln,self.decfile,self.tp_pacer))
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))

    def get_sinc(self):
        return self.sinc

    def set_sinc(self, sinc):
        self.sinc = sinc
        self.set_custom_window(self.sinc*np.hamming(self.nphase*self.nchan))
        self.set_sinc(np.sinc(self.sinc_sample_locations/np.pi))

    def get_psrate(self):
        return self.psrate

    def set_psrate(self, psrate):
        self.psrate = psrate
        self.set_pparamstr("%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (self.psrate/1e3, self.pchanwidth/1e3, self.ifreq/1.0e6,self.samp_rate/1.0e6,self.ebw,self.fbsize))

    def get_pchanwidth(self):
        return self.pchanwidth

    def set_pchanwidth(self, pchanwidth):
        self.pchanwidth = pchanwidth
        self.set_pparamstr("%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (self.psrate/1e3, self.pchanwidth/1e3, self.ifreq/1.0e6,self.samp_rate/1.0e6,self.ebw,self.fbsize))

    def get_gmdate(self):
        return self.gmdate

    def set_gmdate(self, gmdate):
        self.gmdate = gmdate
        self.set_pparam(self.prefix+"-"+self.gmdate+"-psr.params" if self.psrmode != 0 else "/dev/null")
        self.set_psrfilename(self.prefix+"-"+self.gmdate+"-psr.rfb8" if self.psrmode != 0 else "/dev/null")

    def get_ebw(self):
        return self.ebw

    def set_ebw(self, ebw):
        self.ebw = ebw
        self.set_pparamstr("%.2f,%.2f,%.4f,%.4f,%.4f,%d\n" % (self.psrate/1e3, self.pchanwidth/1e3, self.ifreq/1.0e6,self.samp_rate/1.0e6,self.ebw,self.fbsize))

    def get_win(self):
        return self.win

    def set_win(self, win):
        self.win = win
        self.set_winsum(sum(map(lambda x:x*x, self.win)))

    def get_set_baseline(self):
        return self.set_baseline

    def set_set_baseline(self, set_baseline):
        self.set_baseline = set_baseline
        self.set_baseline_set_status(helper.baseline_setter(self.set_baseline))

    def get_pparamstr(self):
        return self.pparamstr

    def set_pparamstr(self, pparamstr):
        self.pparamstr = pparamstr
        self.set_wrstatus(open(self.pparam, "w").write(self.pparamstr))

    def get_pparam(self):
        return self.pparam

    def set_pparam(self, pparam):
        self.pparam = pparam
        self.set_wrstatus(open(self.pparam, "w").write(self.pparamstr))

    def get_ira(self):
        return self.ira

    def set_ira(self, ira):
        self.ira = ira
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        Qt.QMetaObject.invokeMethod(self._ira_line_edit, "setText", Qt.Q_ARG("QString", eng_notation.num_to_str(self.ira)))

    def get_fstop(self):
        return self.fstop

    def set_fstop(self, fstop):
        self.fstop = fstop
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))
        self._fstop_callback(self.fstop)

    def get_frate(self):
        return self.frate

    def set_frate(self, frate):
        self.frate = frate
        self.set_fringe_label((1.0/self.frate))
        self.single_pole_iir_filter_xx_2.set_taps((helper.getalpha(self.frate/2.0,self.fft_hz)))

    def get_fft_probed(self):
        return self.fft_probed

    def set_fft_probed(self, fft_probed):
        self.fft_probed = fft_probed
        self.set_curr_dx(helper.curr_diff(self.fft_probed,self.enable_normalize,self.fftsize,0))
        self.set_curr_dx2(helper.curr_diff(self.fft_probed,self.enable_normalize,self.fftsize,1))
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_fft_hz(self):
        return self.fft_hz

    def set_fft_hz(self, fft_hz):
        self.fft_hz = fft_hz
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))
        self.blocks_keep_one_in_n_1.set_n((int(self.samp_rate/self.fft_hz)))
        self.single_pole_iir_filter_xx_0.set_taps((helper.getalpha(self.fft_hz/2.0,self.fftrate)))
        self.single_pole_iir_filter_xx_0_0.set_taps((helper.getalpha(self.fft_hz/2.0,self.fftrate)))
        self.single_pole_iir_filter_xx_1.set_taps((helper.getalpha(self.fft_hz/2.0,self.samp_rate)))
        self.single_pole_iir_filter_xx_2.set_taps((helper.getalpha(self.frate/2.0,self.fft_hz)))

    def get_fft_avg(self):
        return self.fft_avg

    def set_fft_avg(self, fft_avg):
        self.fft_avg = fft_avg
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_fft2_probed(self):
        return self.fft2_probed

    def set_fft2_probed(self, fft2_probed):
        self.fft2_probed = fft2_probed
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_enable_normalize(self):
        return self.enable_normalize

    def set_enable_normalize(self, enable_normalize):
        self.enable_normalize = enable_normalize
        self.set_curr_dx(helper.curr_diff(self.fft_probed,self.enable_normalize,self.fftsize,0))
        self.set_curr_dx2(helper.curr_diff(self.fft_probed,self.enable_normalize,self.fftsize,1))
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_declination(self):
        return self.declination

    def set_declination(self, declination):
        self.declination = declination
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_dcgain(self):
        return self.dcgain

    def set_dcgain(self, dcgain):
        self.dcgain = dcgain
        self._dcgain_callback(self.dcgain)
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_custom_window(self):
        return self.custom_window

    def set_custom_window(self, custom_window):
        self.custom_window = custom_window
        self.set_save_filter(open("poopy.dat", "w").write(str(list(self.custom_window))))
        self.blocks_multiply_const_vxx_4.set_k(self.custom_window[0:self.nchan])
        self.blocks_multiply_const_vxx_4_0.set_k(self.custom_window[-self.nchan:])
        self.blocks_multiply_const_vxx_4_0_0.set_k(self.custom_window[-self.nchan:])
        self.blocks_multiply_const_vxx_4_2.set_k(self.custom_window[0:self.nchan])

    def get_corr_probed(self):
        return self.corr_probed

    def set_corr_probed(self, corr_probed):
        self.corr_probed = corr_probed
        self.set_fft_log_status(helper.fft_log(self.fft_probed,self.fft2_probed,self.corr_probed,self.ifreq,self.samp_rate,self.longitude,self.enable_normalize,self.prefix,self.declination,self.rfilist,self.dcgain,self.fft_avg,self.mode,self.zerotime,self.decfile,self.tp_interval,self.spec_interval,self.fft_hz))

    def get_clear_baseline(self):
        return self.clear_baseline

    def set_clear_baseline(self, clear_baseline):
        self.clear_baseline = clear_baseline
        self.set_baseline_clear_status(helper.baseline_clearer(self.clear_baseline))

    def get_annotation(self):
        return self.annotation

    def set_annotation(self, annotation):
        self.annotation = annotation
        self.set_anno_status(helper.do_annotation(self.ira,self.declination,self.baseline,self.annotation,self.srate*0.8,self.abw,self.ifreq,self.srate,self.prefix))
        Qt.QMetaObject.invokeMethod(self._annotation_line_edit, "setText", Qt.Q_ARG("QString", str(self.annotation)))

    def get_ang(self):
        return self.ang

    def set_ang(self, ang):
        self.ang = ang
        self.set_frotate(helper.fringe_stop (self.tp_pacer, self.ra, self.decln, self.longitude, self.latitude, self.baseline, self.fstop, self.ang, self.ifreq))

    def get_wrstatus(self):
        return self.wrstatus

    def set_wrstatus(self, wrstatus):
        self.wrstatus = wrstatus

    def get_winsum(self):
        return self.winsum

    def set_winsum(self, winsum):
        self.winsum = winsum

    def get_wchan(self):
        return self.wchan

    def set_wchan(self, wchan):
        self.wchan = wchan
        self._wchan_callback(self.wchan)
        self.blocks_multiply_const_vxx_3.set_k(1.0 if self.wchan == 0 else 0)
        self.blocks_multiply_const_vxx_3_0.set_k(1.0  if self.wchan == 1 else 0.0)

    def get_variable_qtgui_label_0(self):
        return self.variable_qtgui_label_0

    def set_variable_qtgui_label_0(self, variable_qtgui_label_0):
        self.variable_qtgui_label_0 = variable_qtgui_label_0
        Qt.QMetaObject.invokeMethod(self._variable_qtgui_label_0_label, "setText", Qt.Q_ARG("QString", str(self._variable_qtgui_label_0_formatter(self.variable_qtgui_label_0))))

    def get_time_pacer(self):
        return self.time_pacer

    def set_time_pacer(self, time_pacer):
        self.time_pacer = time_pacer

    def get_start_km(self):
        return self.start_km

    def set_start_km(self, start_km):
        self.start_km = start_km
        self.qtgui_vector_sink_f_0.set_x_axis(self.start_km, self.km_incr)

    def get_spec_labels(self):
        return self.spec_labels

    def set_spec_labels(self, spec_labels):
        self.spec_labels = spec_labels

    def get_secondary_lmst_label(self):
        return self.secondary_lmst_label

    def set_secondary_lmst_label(self, secondary_lmst_label):
        self.secondary_lmst_label = secondary_lmst_label
        Qt.QMetaObject.invokeMethod(self._secondary_lmst_label_label, "setText", Qt.Q_ARG("QString", str(self._secondary_lmst_label_formatter(self.secondary_lmst_label))))

    def get_save_filter(self):
        return self.save_filter

    def set_save_filter(self, save_filter):
        self.save_filter = save_filter

    def get_psrfilename(self):
        return self.psrfilename

    def set_psrfilename(self, psrfilename):
        self.psrfilename = psrfilename

    def get_mode_map(self):
        return self.mode_map

    def set_mode_map(self, mode_map):
        self.mode_map = mode_map

    def get_km_incr(self):
        return self.km_incr

    def set_km_incr(self, km_incr):
        self.km_incr = km_incr
        self.qtgui_vector_sink_f_0.set_x_axis(self.start_km, self.km_incr)

    def get_igain(self):
        return self.igain

    def set_igain(self, igain):
        self.igain = igain
        Qt.QMetaObject.invokeMethod(self._igain_line_edit, "setText", Qt.Q_ARG("QString", eng_notation.num_to_str(self.igain)))
        self.osmosdr_source_0.set_gain(self.igain, 0)
        self.osmosdr_source_0.set_gain(self.igain , 1)

    def get_frotate(self):
        return self.frotate

    def set_frotate(self, frotate):
        self.frotate = frotate
        self.blocks_multiply_const_vxx_0.set_k(self.frotate)

    def get_fringe_label(self):
        return self.fringe_label

    def set_fringe_label(self, fringe_label):
        self.fringe_label = fringe_label
        Qt.QMetaObject.invokeMethod(self._fringe_label_label, "setText", Qt.Q_ARG("QString", str(self._fringe_label_formatter(self.fringe_label))))

    def get_fincr(self):
        return self.fincr

    def set_fincr(self, fincr):
        self.fincr = fincr
        self.qtgui_vector_sink_f_0_1.set_x_axis(((self.ifreq-self.samp_rate/2)/1.0e6), self.fincr)

    def get_fftrate(self):
        return self.fftrate

    def set_fftrate(self, fftrate):
        self.fftrate = fftrate
        self.single_pole_iir_filter_xx_0.set_taps((helper.getalpha(self.fft_hz/2.0,self.fftrate)))
        self.single_pole_iir_filter_xx_0_0.set_taps((helper.getalpha(self.fft_hz/2.0,self.fftrate)))

    def get_fft_log_status(self):
        return self.fft_log_status

    def set_fft_log_status(self, fft_log_status):
        self.fft_log_status = fft_log_status

    def get_dcblock(self):
        return self.dcblock

    def set_dcblock(self, dcblock):
        self.dcblock = dcblock
        self._dcblock_callback(self.dcblock)
        self.blocks_multiply_const_vxx_2.set_k(self.dcblock)

    def get_curr_tp_vect(self):
        return self.curr_tp_vect

    def set_curr_tp_vect(self, curr_tp_vect):
        self.curr_tp_vect = curr_tp_vect
        self.blocks_add_const_vxx_0_0.set_k(self.curr_tp_vect[0])
        self.blocks_add_const_vxx_0_0_0.set_k(self.curr_tp_vect[1])

    def get_curr_dx2(self):
        return self.curr_dx2

    def set_curr_dx2(self, curr_dx2):
        self.curr_dx2 = curr_dx2
        self.blocks_add_const_vxx_0_1.set_k(self.curr_dx2)

    def get_curr_dx(self):
        return self.curr_dx

    def set_curr_dx(self, curr_dx):
        self.curr_dx = curr_dx
        self.blocks_add_const_vxx_0.set_k(self.curr_dx)

    def get_clk_deriv(self):
        return self.clk_deriv

    def set_clk_deriv(self, clk_deriv):
        self.clk_deriv = clk_deriv

    def get_baseline_set_status(self):
        return self.baseline_set_status

    def set_baseline_set_status(self, baseline_set_status):
        self.baseline_set_status = baseline_set_status

    def get_baseline_clear_status(self):
        return self.baseline_clear_status

    def set_baseline_clear_status(self, baseline_clear_status):
        self.baseline_clear_status = baseline_clear_status

    def get_anno_status(self):
        return self.anno_status

    def set_anno_status(self, anno_status):
        self.anno_status = anno_status

    def get_actual_dec_label(self):
        return self.actual_dec_label

    def set_actual_dec_label(self, actual_dec_label):
        self.actual_dec_label = actual_dec_label
        Qt.QMetaObject.invokeMethod(self._actual_dec_label_label, "setText", Qt.Q_ARG("QString", str(self._actual_dec_label_formatter(self.actual_dec_label))))



def argument_parser():
    parser = ArgumentParser()
    parser.add_argument(
        "--abw", dest="abw", type=eng_float, default=eng_notation.num_to_str(float(4.0e6)),
        help="Set Analog  bandwidth [default=%(default)r]")
    parser.add_argument(
        "--antenna", dest="antenna", type=str, default='RX2',
        help="Set Antenna [default=%(default)r]")
    parser.add_argument(
        "--baseline", dest="baseline", type=eng_float, default=eng_notation.num_to_str(float(20)),
        help="Set Baseline length [default=%(default)r]")
    parser.add_argument(
        "--bbgain", dest="bbgain", type=eng_float, default=eng_notation.num_to_str(float(5)),
        help="Set Baseband Gain [default=%(default)r]")
    parser.add_argument(
        "--clock", dest="clock", type=str, default='default',
        help="Set Clock Source [default=%(default)r]")
    parser.add_argument(
        "--dcg", dest="dcg", type=intx, default=100,
        help="Set Detector DC Gain [default=%(default)r]")
    parser.add_argument(
        "--decln", dest="decln", type=eng_float, default=eng_notation.num_to_str(float(0)),
        help="Set Observing Declination [default=%(default)r]")
    parser.add_argument(
        "--dfreq", dest="dfreq", type=eng_float, default=eng_notation.num_to_str(float(0.0)),
        help="Set Alternet Doppler Cente Frequency [default=%(default)r]")
    parser.add_argument(
        "--fbsize", dest="fbsize", type=intx, default=128,
        help="Set PSR Filterbank size [default=%(default)r]")
    parser.add_argument(
        "--fftsize", dest="fftsize", type=intx, default=2048,
        help="Set FFT size [default=%(default)r]")
    parser.add_argument(
        "--frequency", dest="frequency", type=eng_float, default=eng_notation.num_to_str(float(1420.4058e6)),
        help="Set Center Frequency [default=%(default)r]")
    parser.add_argument(
        "--gain", dest="gain", type=eng_float, default=eng_notation.num_to_str(float(30)),
        help="Set RF Gain [default=%(default)r]")
    parser.add_argument(
        "--ifgain", dest="ifgain", type=eng_float, default=eng_notation.num_to_str(float(5)),
        help="Set IF Gain [default=%(default)r]")
    parser.add_argument(
        "--integration", dest="integration", type=eng_float, default=eng_notation.num_to_str(float(0.5)),
        help="Set Integration Time (Sec.) [default=%(default)r]")
    parser.add_argument(
        "--latitude", dest="latitude", type=eng_float, default=eng_notation.num_to_str(float(44.9)),
        help="Set Local Latitude [default=%(default)r]")
    parser.add_argument(
        "--longitude", dest="longitude", type=eng_float, default=eng_notation.num_to_str(float((-76.03))),
        help="Set Local Longitude [default=%(default)r]")
    parser.add_argument(
        "--ppstime", dest="ppstime", type=str, default='internal',
        help="Set Time Source [default=%(default)r]")
    parser.add_argument(
        "--psrmode", dest="psrmode", type=intx, default=0,
        help="Set Enable PSR mode [default=%(default)r]")
    parser.add_argument(
        "--ra", dest="ra", type=eng_float, default=eng_notation.num_to_str(float(12.0)),
        help="Set Target RA [default=%(default)r]")
    parser.add_argument(
        "--spec-interval", dest="spec_interval", type=intx, default=15,
        help="Set Spectral Logging Interval [default=%(default)r]")
    parser.add_argument(
        "--srate", dest="srate", type=eng_float, default=eng_notation.num_to_str(float(2.50e6)),
        help="Set Sample rate [default=%(default)r]")
    parser.add_argument(
        "--tp-interval", dest="tp_interval", type=intx, default=2,
        help="Set TP Logging Interval [default=%(default)r]")
    parser.add_argument(
        "--zerotime", dest="zerotime", type=eng_float, default=eng_notation.num_to_str(float(99.3)),
        help="Set SIdereal time for auto baseline set [default=%(default)r]")
    return parser


def main(top_block_cls=SpectroRadiometer, options=None):
    if options is None:
        options = argument_parser().parse_args()

    qapp = Qt.QApplication(sys.argv)

    tb = top_block_cls(abw=options.abw, antenna=options.antenna, baseline=options.baseline, bbgain=options.bbgain, clock=options.clock, dcg=options.dcg, decln=options.decln, dfreq=options.dfreq, fbsize=options.fbsize, fftsize=options.fftsize, frequency=options.frequency, gain=options.gain, ifgain=options.ifgain, integration=options.integration, latitude=options.latitude, longitude=options.longitude, ppstime=options.ppstime, psrmode=options.psrmode, ra=options.ra, spec_interval=options.spec_interval, srate=options.srate, tp_interval=options.tp_interval, zerotime=options.zerotime)

    tb.start()

    tb.show()

    def sig_handler(sig=None, frame=None):
        tb.stop()
        tb.wait()

        Qt.QApplication.quit()

    signal.signal(signal.SIGINT, sig_handler)
    signal.signal(signal.SIGTERM, sig_handler)

    timer = Qt.QTimer()
    timer.start(500)
    timer.timeout.connect(lambda: None)

    qapp.exec_()

if __name__ == '__main__':
    main()
