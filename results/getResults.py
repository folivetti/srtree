import numpy as np
import pandas as pd 
import sys 

folder = sys.argv[1]

runs = []
for i in range(1,51):
   try:
       df = pd.read_csv(f"{folder}/run_{i}.csv")
       if len(df)==0:
           continue
       runs.append(df.MSE_train.min())
       print(df.MSE_train.min(), df.loc[df.MSE_train.argmin(),"Expression"])
   except:
       pass
print(np.mean(runs), np.std(runs), np.min(runs))
