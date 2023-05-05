import pandas as pd
from collections import defaultdict
import matplotlib.pyplot as plt

dname = "bench_balanced2"
df = pd.read_csv(f"{dname}.csv")

names = df.Name.values
means = df.Mean.values

data = defaultdict(list)

for n, m in zip(names, means):
    algo = n.strip().split("/")[-1]
    data[algo].append(m)

df_plot = pd.DataFrame(data, index = list(range(10, 1001, 10)))
df_plot.plot()
plt.savefig(f"{dname}.png")
'''
data = defaultdict(list)
for n, m in zip(names, means):
    algo = n.strip().split("/")[-1]
    if algo == "grad" or algo == "autodiff":
        data[algo].append(m)

df_plot = pd.DataFrame(data)
df_plot.plot()
plt.savefig(f"{dname}_rev.png")
'''
