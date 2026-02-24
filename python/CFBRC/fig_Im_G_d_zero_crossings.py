import numpy as np
import matplotlib.pyplot as plt

# cfbrc.py から関数を使う（同じフォルダに置く）
from cfbrc import G_real_im_no_complex


def detect_zero_crossings(theta, y):
    """
    y(theta) の零交差を符号反転で検出し、線形補間で近似解を返す。
    y==0 の格子点がある場合の重複を避けるため少し丁寧に処理。
    """
    zeros = []

    s = np.sign(y)
    # y==0 の点をそのまま採用（ただし重複回避）
    exact = np.where(s == 0)[0]
    for i in exact:
        tz = float(theta[i])
        if (not zeros) or abs(zeros[-1] - tz) > 1e-12:
            zeros.append(tz)

    # 符号反転区間
    for i in range(len(theta) - 1):
        y0, y1 = y[i], y[i + 1]
        if y0 == 0 or y1 == 0:
            continue
        if y0 * y1 < 0:
            t0, t1 = theta[i], theta[i + 1]
            # 線形補間
            tz = float(t0 - y0 * (t1 - t0) / (y1 - y0))
            # 近接重複を除去
            if (not zeros) or abs(zeros[-1] - tz) > 1e-10:
                zeros.append(tz)

    return np.array(zeros, dtype=float)


def theoretical_zeros_even_d(x, d):
    """
    偶数 d のときの理論零点: theta = x * tan(k*pi/d)
    k = -(d/2-1),...,0,...,(d/2-1) で個数 d-1。
    """
    assert d % 2 == 0, "theoretical_zeros_even_d は偶数 d 専用"
    ks = np.arange(-(d // 2 - 1), (d // 2 - 1) + 1, dtype=int)
    return x * np.tan(ks * np.pi / d)


def plot_imG_with_zeros(
    x=1.0,
    d=8,
    theta_min=-3.0,
    theta_max=3.0,
    n=40001,
    out_png="__fig#imG_zeros-v1-default.png",
):
    theta = np.linspace(theta_min, theta_max, n)

    # Im G_d(x, theta) を実数演算で計算
    imG = np.array([G_real_im_no_complex(x, th, d)[1] for th in theta], dtype=float)

    # 検出零点（符号反転＋線形補間）
    zeros_det = detect_zero_crossings(theta, imG)

    # 理論零点（偶数 d のときのみ）
    zeros_th = None
    if d % 2 == 0:
        zeros_th = theoretical_zeros_even_d(x, d)
        # 表示範囲に入るものだけ
        zeros_th = zeros_th[(zeros_th >= theta_min) & (zeros_th <= theta_max)]

    # ---- Plot ----
    plt.figure(figsize=(10, 4))
    plt.axhline(0.0, linewidth=1)

    # plt.plot(theta, imG, linewidth=0.5, label=r"$\Im\,G_d(x,\theta)$")
    plt.plot(
        theta,
        imG,
        linewidth=1.6,
        antialiased=True,
        solid_joinstyle="round",
        label=r"$\Im\,G_d(x,\theta)$",
    )  # 高品質版

    if zeros_det.size > 0:
        plt.scatter(zeros_det, np.zeros_like(zeros_det), s=30, label="detected zeros")

    if zeros_th is not None and zeros_th.size > 0:
        plt.scatter(
            zeros_th,
            np.zeros_like(zeros_th),
            marker="x",
            s=60,
            label=r"theory: $\theta=x\tan(k\pi/d)$",
        )

    plt.title(f"Im G_d zero crossings  (x={x}, d={d})")
    plt.xlabel(r"$\theta$")
    plt.ylabel(r"$\Im\,G_d$")
    plt.yscale("symlog", linthresh=0.01)  # symlog で小さい値も見えるように
    plt.legend(loc="lower center", fontsize=10)
    plt.tight_layout()
    plt.savefig(out_png, dpi=300)
    plt.close()

    # ログ表示（論文の検算にも使える）
    print(f"[saved] {out_png}")
    print(f"detected zeros: {len(zeros_det)}")
    if zeros_th is not None:
        print(f"theoretical zeros in range: {len(zeros_th)}")
        # 近い順に比較（参考）
        if len(zeros_det) > 0 and len(zeros_th) > 0:
            m = min(len(zeros_det), len(zeros_th))
            det_sorted = np.sort(zeros_det)[:m]
            th_sorted = np.sort(zeros_th)[:m]
            max_abs = np.max(np.abs(det_sorted - th_sorted))
            print(f"max |det-theory| (first {m}): {max_abs:.3e}")


if __name__ == "__main__":
    # 例：論文の図に合わせて適宜調整
    plot_imG_with_zeros(
        x=1,
        d=8,  # 偶数推奨（理論点が出せる）
        theta_min=-3.0,
        theta_max=3.0,
        n=40001,
        out_png="__fig#imG_zeros-v1.png",
    )
