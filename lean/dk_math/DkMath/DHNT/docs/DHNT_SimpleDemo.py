import numpy as np

"""
動的調和数論：

等差数列生成アルゴリズム
    i = index: 0 base index

解説：
    古典的な等差数列の生成
    古典的な式: a_n = a_0 + d * i

    動的調和数論 等差数列の生成（古典的な方法を拡張した）
    古典的な式: a_n = a_0 + d * i
    拡張した式: a_n = a_0 + d * f(x) * i, f(x) = ln(e^x), x = 1, d = 1 で自然数列 N となる
    
    動的調和係数 k: f(k) = ln(e^k)

    つまり、

    動的調和数論 等差数列の生成（k スケール版）
    N_i_k = a_0 + f(k) * i
    N_i_k = a_0 + ln(e^k) * i

    となり、k によるスケールが可能となる。

    また、k は f(i) としても表現可能である。

    N_i_k = a_0 + ln(e^f(i)) * i
"""


def round_float_np(value: float, round_digit: int = 2):
    """
    浮動小数点数の丸め（numpy.round 四捨五入）

    :param value: 浮動小数点数
    :param round_digit: 丸め桁数 (default: 2)
    :return: 丸めた値
    """
    return np.round(value, round_digit)


def round_float_int(value: float, round_digit: int = 2, base: int = 10):
    """
    浮動小数点数の丸め（切り捨て）

    :param value: 浮動小数点数
    :param round_digit: 丸め桁数 (default: 2)
    :param base: 丸め基数 (default: 10)
    :return: 丸めた値
    """
    rd = base**round_digit  # 10進数での丸め桁数
    return int(value * rd) / rd


def round_float(value: float, round_digit: int = 2, base: int = 10, lib: str = None):
    """
    浮動小数点数の丸め（四捨五入）

    :param value: 浮動小数点数
    :param round_digit: 丸め桁数 (default: 2)
    :param base: 丸め基数 (default: 10)
    :return: 丸めた値
    """
    if lib == "numpy":
        return round_float_np(value, round_digit)
    elif lib == "int":
        return round_float_int(value, round_digit, base)
    else:
        return round(value, round_digit)


def ln(value: float):
    """
    自然対数（ネイピア数）

    :param value: 値
    :return: 自然対数
    """
    return np.log(value)


def ln_e(value: float):
    """
    ネイピア数の自然対数

    :param value: 値
    :return: 自然対数
    """
    return ln(np.exp(value))


def classic_arithmetic_sequence(a: float, d: float, n: int = 10):
    """
    古典的な等差数列の生成

    古典的な式: a_n = a_0 + d * i

    :param a: 初項 a_0
    :param d: 公差
    :param n: 項数 (default: 10)
    :return: 等差数列
    """
    return [round_float(a + d * i) for i in range(n)]
    # prototype code:
    # return [int((a + (i * d)) * ROUND) / ROUND for i in range(n)]


def dynamic_arithmetic_sequence_c(a: float, d: float, k: float = 1.0, n: int = 10):
    """
    動的調和数論 等差数列の生成（古典的な方法を拡張したのみ）

    古典的な式: a_n = a_0 + d * i
    拡張した式: a_n = a_0 + x * d * i, x = 1 = ln(e^1)
    動的調和 k: k = x = ln(e^k)

    N_i_k = a + ln(e^k) * i * d

    :param a: 初項
    :param d: 公差
    :param k: スケール因子 (default: 1.0)
    :param n: 項数 (default: 10)
    :return: 動的調和数列
    """
    scale_factor = ln_e(k)  # ln(e^k) = k
    return [round_float(a + scale_factor * i * d) for i in range(n)]
    # prototype code:
    # scale_factor = np.log(np.exp(k))  # ln(e^k) = k
    # return [int((a + scale_factor * (i * d)) * ROUND) / ROUND for i in range(n)]


def _das(a: float, k: float, n: int = 10):
    """
    動的調和数論 等差数列の生成（k スケール版）
    N_i_k = a + ln(e^k) * n
    """

    """
    # スケール因子の計算
    # ln(e^k) = k であるが、ここに現れる e はネイピア数。
    # e は定数である一方で、e^x の形では変数（関数）としての動きを示す。
    # そのため、このステップを省略せず記述する。
    """
    scale_factor = ln_e(k)  # ln(e^k) = k
    return [round_float(a + scale_factor * i) for i in range(n)]
    # prototype code:
    # scale_factor = np.log(np.exp(k))  # ln(e^k) = k
    # return [int((a + scale_factor * i) * ROUND) / ROUND for i in range(n)]


def dynamic_arithmetic_sequence_d(a: float, d: float, k: float = 1.0, n: int = 10):
    """
    動的調和数論 等差数列の生成（d スケール版）

    :param a: 初項
    :param d: 公差
    :param k: スケール因子 (default: 1.0)
    :param n: 項数 (default: 10)
    :return: 動的調和数列
    """
    _k = d * k  # k' = 公差 * スケール因子
    return _das(a, _k, n)


def dynamic_arithmetic_sequence_k(a: float, k: float, n: int = 10):
    """
    動的調和数論 等差数列の生成（k スケール版）

    :param a: 初項
    :param k: スケール因子（k = d * scale）
    :param n: 項数 (default: 10)
    :return: 動的調和数列
    """
    return _das(a, k, n)


def demo():
    # 使用例
    a = 1  # 初項
    d = 2  # 公差 (※実際の公差＝公差・スケール因子)
    k = 1.0  # スケール因子
    n = 10  # 項数

    print("動的調和数論:", "等差数列:", "デモ")

    print(
        f"""
a = {a}\t# 初項
d = {d}\t# 公差 (※実際の公差＝公差・スケール因子)
k = {k}\t# スケール因子
n = {n}\t# 項数
""".strip()
    )

    print(
        "パラメータ:",
        "(a, d, k, n) =",
        (
            a,
            d,
            k,
            n,
        ),
    )
    sequence = dynamic_arithmetic_sequence_c(a, d, k, n)
    print("等差数列（古典版:c）:", sequence)
    print("等差数列（拡張版:d）:", dynamic_arithmetic_sequence_d(a, d, k, n))
    # d は無い k = d * k スケールのみ、ゆえに。
    k = d * k
    print("等差数列（拡張版:k）:", dynamic_arithmetic_sequence_k(a, k, n))
    print()
    print("古典的な等差数列の例:", classic_arithmetic_sequence(a, d, n))
    print()


def test():
    N = 10

    """
    param: (a, d, k)
    a: 初項
    d: 等差
    k: スケール
    """
    params = [
        (1, 1, 0),
        (1, 0, 1),
        (1, 5, 1),
        (3, 5, 1),
        (3, 5.1, 1),
        (3, 5.2, 1),
        (3, 5, 1.02),
        (3, 5, 1.04),
    ]

    for a, d, k in params:
        print(
            "パラメータ:",
            "(a, d, k) =",
            (
                a,
                d,
                k,
            ),
        )
        print("等差数列（古典版:c）:", dynamic_arithmetic_sequence_c(a, d, k, N))
        print("等差数列（拡張版:d）:", dynamic_arithmetic_sequence_d(a, d, k, N))
        # d は無い k = d * k スケールのみ、ゆえに。
        k = d * k
        print("等差数列（拡張版:k）:", dynamic_arithmetic_sequence_k(a, k, N))
        print()


if __name__ == "__main__":
    demo()
    test()


"""
実行結果の例：

動的調和数論: 等差数列: デモ
a = 1   # 初項
d = 2   # 公差 (※実際の公差＝公差・スケール因子)
k = 1.0 # スケール因子
n = 10  # 項数
パラメータ: (a, d, k, n) = (1, 2, 1.0, 10)
等差数列（古典版:c）: [1.0, 3.0, 5.0, 7.0, 9.0, 11.0, 13.0, 15.0, 17.0, 19.0]
等差数列（拡張版:d）: [1.0, 3.0, 5.0, 7.0, 9.0, 11.0, 13.0, 15.0, 17.0, 19.0]
等差数列（拡張版:k）: [1.0, 3.0, 5.0, 7.0, 9.0, 11.0, 13.0, 15.0, 17.0, 19.0]

古典的な等差数列の例: [1, 3, 5, 7, 9, 11, 13, 15, 17, 19]

パラメータ: (a, d, k) = (1, 1, 0)
等差数列（古典版:c）: [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
等差数列（拡張版:d）: [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
等差数列（拡張版:k）: [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]

パラメータ: (a, d, k) = (1, 0, 1)
等差数列（古典版:c）: [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
等差数列（拡張版:d）: [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
等差数列（拡張版:k）: [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]

パラメータ: (a, d, k) = (1, 5, 1)
等差数列（古典版:c）: [1.0, 6.0, 11.0, 16.0, 21.0, 26.0, 31.0, 36.0, 41.0, 46.0]
等差数列（拡張版:d）: [1.0, 6.0, 11.0, 16.0, 21.0, 26.0, 31.0, 36.0, 41.0, 46.0]
等差数列（拡張版:k）: [1.0, 6.0, 11.0, 16.0, 21.0, 26.0, 31.0, 36.0, 41.0, 46.0]

パラメータ: (a, d, k) = (3, 5, 1)
等差数列（古典版:c）: [3.0, 8.0, 13.0, 18.0, 23.0, 28.0, 33.0, 38.0, 43.0, 48.0]
等差数列（拡張版:d）: [3.0, 8.0, 13.0, 18.0, 23.0, 28.0, 33.0, 38.0, 43.0, 48.0]
等差数列（拡張版:k）: [3.0, 8.0, 13.0, 18.0, 23.0, 28.0, 33.0, 38.0, 43.0, 48.0]

パラメータ: (a, d, k) = (3, 5.1, 1)
等差数列（古典版:c）: [3.0, 8.1, 13.2, 18.3, 23.4, 28.5, 33.6, 38.7, 43.8, 48.9]
等差数列（拡張版:d）: [3.0, 8.1, 13.2, 18.3, 23.4, 28.5, 33.6, 38.7, 43.8, 48.9]
等差数列（拡張版:k）: [3.0, 8.1, 13.2, 18.3, 23.4, 28.5, 33.6, 38.7, 43.8, 48.9]

パラメータ: (a, d, k) = (3, 5.2, 1)
等差数列（古典版:c）: [3.0, 8.2, 13.4, 18.6, 23.8, 29.0, 34.2, 39.4, 44.6, 49.8]
等差数列（拡張版:d）: [3.0, 8.2, 13.4, 18.6, 23.8, 29.0, 34.2, 39.4, 44.6, 49.8]
等差数列（拡張版:k）: [3.0, 8.2, 13.4, 18.6, 23.8, 29.0, 34.2, 39.4, 44.6, 49.8]

パラメータ: (a, d, k) = (3, 5, 1.02)
等差数列（古典版:c）: [3.0, 8.1, 13.2, 18.3, 23.4, 28.5, 33.6, 38.7, 43.8, 48.9]
等差数列（拡張版:d）: [3.0, 8.1, 13.2, 18.3, 23.4, 28.5, 33.6, 38.7, 43.8, 48.9]
等差数列（拡張版:k）: [3.0, 8.1, 13.2, 18.3, 23.4, 28.5, 33.6, 38.7, 43.8, 48.9]

パラメータ: (a, d, k) = (3, 5, 1.04)
等差数列（古典版:c）: [3.0, 8.2, 13.4, 18.6, 23.8, 29.0, 34.2, 39.4, 44.6, 49.8]
等差数列（拡張版:d）: [3.0, 8.2, 13.4, 18.6, 23.8, 29.0, 34.2, 39.4, 44.6, 49.8]
等差数列（拡張版:k）: [3.0, 8.2, 13.4, 18.6, 23.8, 29.0, 34.2, 39.4, 44.6, 49.8]
"""
