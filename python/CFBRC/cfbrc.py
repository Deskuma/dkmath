#!/usr/bin/env python3
# -*- coding: utf-8 -*-
## Additional experiment: numerical plots and real-axis crossings for even d #4

import numpy as np
import matplotlib.pyplot as plt
from fig_config import fig4_config


# ※再定義
# --- Helpers: "real-only complex" as pair (a,b) ---
def re_im_binom(x, th, d):
    # Re/Im of (x + i*th)^d via even/odd binomial separation
    # Re = sum_{m} C(d,2m)(-1)^m x^{d-2m} th^{2m}
    # Im = sum_{m} C(d,2m+1)(-1)^m x^{d-(2m+1)} th^{2m+1}
    from math import comb

    Re = 0.0
    Im = 0.0
    for m in range(0, d // 2 + 1):
        k = 2 * m
        Re += comb(d, k) * ((-1.0) ** m) * (x ** (d - k)) * (th**k)
    for m in range(0, (d - 1) // 2 + 1):
        k = 2 * m + 1
        Im += comb(d, k) * ((-1.0) ** m) * (x ** (d - k)) * (th**k)
    return Re, Im


import math


# --- G without complex numbers ---
def G_real_im_no_complex(x, theta, d):
    # re_im_binom は既に定義済みとする（スカラー theta）
    Re, Im = re_im_binom(x, theta, d)
    th_pow = theta**d
    r = d % 4
    if r == 0:
        ir_real, ir_imag = 1.0, 0.0
    elif r == 1:
        ir_real, ir_imag = 0.0, 1.0
    elif r == 2:
        ir_real, ir_imag = -1.0, 0.0
    else:  # r == 3
        ir_real, ir_imag = 0.0, -1.0
    ReG = Re - ir_real * th_pow
    ImG = Im - ir_imag * th_pow
    return ReG, ImG


# --- G magnitude without complex numbers ---
def G_abs_no_complex(x, theta, d):
    ReG, ImG = G_real_im_no_complex(x, theta, d)
    return math.hypot(ReG, ImG)


def G_real_im_no_complex_scalar(x, theta, d):
    # re_im_binom がスカラー theta を受け取る前提
    Re, Im = re_im_binom(x, theta, d)
    th_pow = theta**d
    r = d % 4
    if r == 0:
        ir_real, ir_imag = 1.0, 0.0
    elif r == 1:
        ir_real, ir_imag = 0.0, 1.0
    elif r == 2:
        ir_real, ir_imag = -1.0, 0.0
    else:  # r == 3
        ir_real, ir_imag = 0.0, -1.0
    ReG = Re - ir_real * th_pow
    ImG = Im - ir_imag * th_pow
    return ReG, ImG


def magnitude_from_reim(Re, Im):
    return math.sqrt(Re * Re + Im * Im)


def G_no_lib(x, thetas, d, binom=True):
    """
    thetas: 単一スカラー または iterable（list, tuple, range...）
    binom=True: 冪展開を用いて実部/虚部を愚直に計算（複素数型は使わない）
    返り値:
      - スカラー入力 -> (ReG, ImG, Abs)
      - iterable -> (list_Re, list_Im, list_Abs)
    """
    # スカラー判定
    is_iter = False
    try:
        iter(thetas)
        # ただし str は除外
        if isinstance(thetas, (str, bytes)):
            is_iter = False
        else:
            is_iter = True
    except TypeError:
        is_iter = False

    if not is_iter:
        if binom:
            ReG, ImG = G_real_im_no_complex_scalar(x, thetas, d)
            return ReG, ImG, magnitude_from_reim(ReG, ImG)
        else:
            z = x + 1j * thetas
            Z = z**d - (1j * thetas) ** d
            return Z.real, Z.imag, abs(Z)
    else:
        Re_list = []
        Im_list = []
        Abs_list = []
        if binom:
            for t in thetas:
                ReG, ImG = G_real_im_no_complex_scalar(x, t, d)
                Re_list.append(ReG)
                Im_list.append(ImG)
                Abs_list.append(magnitude_from_reim(ReG, ImG))
        else:
            for t in thetas:
                z = x + 1j * t
                Z = z**d - (1j * t) ** d
                Re_list.append(Z.real)
                Im_list.append(Z.imag)
                Abs_list.append(abs(Z))
        return Re_list, Im_list, Abs_list


# --- G as complex number ---
def G_complex(x, theta, d, binom=True):
    return G_no_lib(x, theta, d, binom=binom)


# -- Angle calculation ---
def my_angle(Re, Im):
    return np.arctan2(Im, Re)


# --- Plotting function ---
def plot_G_plots(d, x, thetas, binom=False):

    # Format d and x to two decimal places for filenames and titles
    ds = f"{d:.2f}"
    xs = f"{x:.2f}"

    df = float(ds)
    xf = float(xs)

    dx = f"d{df:.2f}-x{xf:.2f}"

    if fig4_config:
        fig_dpi = fig4_config.dpi
    else:
        raise ValueError("fig_config is not defined.")

    show = False  # Override to not show plots interactively
    print(f"Plotting G plots for d={ds}, x={xs}, binom={binom}, show={show}")

    # Compute G
    (Re, Im, Abs) = G_complex(x, thetas, d, binom=binom)
    Arg = my_angle(Re, Im)

    # Plot 1: Parametric curve in the complex plane
    plt.figure(figsize=(10, 6))
    plt.plot(Re, Im)
    plt.gca().set_aspect("equal", "box")
    plt.title(f"Parametric curve of G(theta): d={ds}, x={xs}")
    plt.xlabel("Re(G)")
    plt.ylabel("Im(G)")
    plt.grid(True)
    plt.savefig(
        fig4_config.filename("4-1_G_parametric_curve", dx, binom=binom),
        dpi=fig_dpi,
        bbox_inches="tight",
    )
    plt.show() if show else None

    # Plot 2: Phase vs theta
    plt.figure(figsize=(10, 6))
    plt.plot(thetas, Arg)
    plt.title(f"arg(G) vs theta: d={ds}, x={xs}")
    plt.xlabel("theta")
    plt.ylabel("arg(G) [rad]")
    plt.grid(True)
    plt.savefig(
        fig4_config.filename("4-2_G_phase_vs_theta", dx, binom=binom),
        dpi=fig_dpi,
        bbox_inches="tight",
    )
    plt.show() if show else None

    # Plot 2: Phase vs theta (unwrapped)
    plt.figure(figsize=(10, 6))
    plt.plot(thetas, np.unwrap(Arg))
    # x = 0 の差表値をラベルに追加
    x0value = np.unwrap(Arg)[thetas.size // 2]
    x_unwrap_max = np.max(np.unwrap(Arg))
    y_pi = int(x0value / (np.pi))
    div_pi = int(x_unwrap_max / (np.pi))
    plt.axvline(
        x=0,
        color="r",
        linestyle="--",
        label=f"x=0, y={x0value:.7f}({div_pi}" + r"$\pi$)",
    )
    plt.legend()

    plt.title(f"arg(G) vs theta (unwrapped): d={ds}, x={xs}")
    plt.xlabel("theta")
    plt.ylabel("arg(G) [rad]")
    plt.grid(True)
    plt.savefig(
        fig4_config.filename("4-2_G_phase_vs_theta_unwrapped", dx, binom=binom),
        dpi=fig_dpi,
        bbox_inches="tight",
    )
    plt.show() if show else None

    # Plot 3: Magnitude vs theta
    plt.figure(figsize=(10, 6))
    plt.plot(thetas, Abs)
    plt.title(f"|G| vs theta: d={ds}, x={xs}")
    plt.xlabel("theta")
    plt.ylabel("|G|")
    plt.grid(True)
    plt.savefig(
        fig4_config.filename("4-3_G_magnitude_vs_theta", dx, binom=binom),
        dpi=fig_dpi,
        bbox_inches="tight",
    )
    plt.show() if show else None

    plt.close("all")


# Multiple plots for d=2,4,8
# Parameters
n = [1, 2, 3]  # 2^n
d = [2**ni for ni in n]
x = [1.0, 2.0, 3.0, 4.0]
thetas = np.linspace(-6.0, 6.0, 3000)
algo_binom = 1 == 1  # True: binomial, False: complex power
multi_plots = 1 == 0  # True: multiple plots, False: single plot
delta_plots = 0.1  # x 増分（delta_plots=0 で無効）

if multi_plots:
    for di in d:
        for xi in x:
            plot_G_plots(di, xi, thetas, binom=algo_binom)
else:
    if delta_plots > 0.0:
        for x in np.arange(0.0, 10 + delta_plots, delta_plots):
            plot_G_plots(8, x, thetas, binom=True)
            plot_G_plots(8, x, thetas, binom=False)
    else:
        plot_G_plots(8, 1.0, thetas, binom=True)
        plot_G_plots(8, 1.0, thetas, binom=False)

# --- Find approximate Im(G)=0 crossings for d=8, x=1.0 ---
d = 8
x = 1.0
(Re, Im, Abs) = G_complex(x, thetas, d, binom=algo_binom)
Arg = my_angle(Re, Im)

# Find approximate Im(G)=0 crossings (phase-lock candidates on the real axis)
sgn = np.sign(Im)
zero_cross_idx = np.where(np.diff(sgn) != 0)[0]

zeros = []
for i in zero_cross_idx:
    t0, t1 = thetas[i], thetas[i + 1]
    y0, y1 = Im[i], Im[i + 1]
    if y1 != y0:
        tz = t0 - y0 * (t1 - t0) / (y1 - y0)
        zeros.append(tz)

# Output the found zeros
zeros = np.array(zeros)
print("Approximate Im(G)=0 crossings for d=8, x=1.0:\n", str(zeros[:12]), len(zeros))
