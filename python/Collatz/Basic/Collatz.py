# Calculate the trajectory of the Collatz conjecture.


def collatz_conjecture(n):
    """
    指定された数 n に対するコラッツ予想の軌跡を計算する関数
    """
    if n <= 0:
        raise ValueError("1以上の正の整数を入力してください。")

    sequence = [n]  # 途中の値を記録するリスト

    s = ""
    while n > 1:
        if n % 2 == 0:
            n = n // 2  # 偶数の場合：2で割る
            s = "E"
        else:
            n = 3 * n + 1  # 奇数の場合：3倍して1を足す
            s = "O"
        sequence.append(n)

    return sequence


# --- 実行テスト ---
start_number = 7
result = collatz_conjecture(start_number)

print(f"開始数字: {start_number}")
print(f"ステップ数: {len(result) - 1}")
print(f"軌跡: {result}")

# ビット観測窓 W_5
for n in result:
    print(f"%10s" % ("-" * 30 + (bin(n).replace("0b", "")))[-5:])
