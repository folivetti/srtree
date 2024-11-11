from pyoperon.sklearn import SymbolicRegressor
import pandas as pd 
from sklearn.model_selection import train_test_split, cross_val_score

df = pd.read_csv("datasets/192_vineyard.tsv.gz", delimiter="\t")
X = df[["lugs_1989", "lugs_1990"]].values
y = df.target.values 

X_train, X_test, y_train, y_test = train_test_split(X, y, train_size=0.7)

reg = SymbolicRegressor(
        allowed_symbols= "add,sub,mul,div,log,exp,sqrt,abs,sin,cos,constant,variable",
        brood_size= 10,
        comparison_factor= 0,
        crossover_internal_probability= 0.9,
        crossover_probability= 1.0,
        epsilon= 1e-05,
        female_selector= "tournament",
        generations= 9,
        initialization_max_depth= 10,
        initialization_max_length= 100,
        initialization_method= "btc",
        irregularity_bias= 0.0,
        optimizer_iterations= 50,
        optimizer='lbfgs',
        male_selector= "tournament",
        max_depth= 10,
        max_evaluations= 100000000000,
        max_length= 100,
        max_selection_pressure= 100,
        model_selection_criterion= "minimum_description_length",
        mutation_probability= 0.25,
        n_threads= 32,
        objectives= [ 'r2', 'length' ],
        offspring_generator= "basic",
        pool_size= 1000,
        population_size= 1000,
        random_state= None,
        reinserter= "keep-best",
        time_limit= 900,
        tournament_size= 3,
        )
reg.fit(X_train, y_train)
res = [(s['objective_values'], s['tree'], s['minimum_description_length']) for s in reg.pareto_front_]

for obj, expr, mdl in res:
    print(obj, mdl, reg.get_model_string(expr, 16))

