import numpy as np
import matplotlib.pyplot as plt

from CosmicComplex import CosmicComplex, unwrap

cc = CosmicComplex(d=8, x=4.0, mode="even")

# 1) theta グリッド
T = 6.0
N = 2001
thetas = np.linspace(-T, T, N)

# 2) arg の系列を取る
args = [cc.observe(float(th)).arg for th in thetas]

# 3) unwrap して連続化
args_u = np.array(unwrap(args))

# 4) 数値微分（位相速度）
darg = np.gradient(args_u, thetas)

# 5) 描画：theta vs d/dtheta arg(G)
plt.figure(figsize=(10, 6))
plt.plot(thetas, darg)
plt.grid(True)
plt.xlabel("theta")
plt.ylabel("d/dtheta arg(G(theta))")
plt.title(
    "Phase derivative (unwrapped)\n"
    + f"(CosmicComplex d={cc.params.d}, x={cc.params.x}, mode='{cc.mode}')"
)
plt.savefig("__fig#phase_derivative_unwrapped-v0.png", dpi=150)
