# tiny genetic programming by © moshe sipper, www.moshesipper.com
# modified by fabricio olivetti:
# - supports parameter optimization
# - supports unary functions
# - easier to add new functions with different arity
# - maximum number of nodes during initialization and during cx/mut (we repeat the operator until finding a child that respects the max size)
# - uses numpy instead of list
# - print_expr method that prints as a math expression
# - support to multiple variables
# - support to autodiff
# TODO: two variables, roxy
from copy import deepcopy
import numpy as np
from scipy.optimize import minimize, approx_fprime
import pandas as pd
from collections import defaultdict

POP_SIZE        = 200   # population size
MIN_DEPTH       = 2    # minimal initial random tree depth
MAX_DEPTH       = 4    # maximal initial random tree depth
GENERATIONS     = 500  # maximal number of generations to run evolution
TOURNAMENT_SIZE = 2    # size of tournament for tournament selection
XO_RATE         = 1.0  # crossover rate
PROB_MUTATION   = 0.25  # per-node mutation probability
MAX_SIZE        = 10
rng = np.random.default_rng()

def add(x, y): return x + y
def sub(x, y): return x - y
def mul(x, y): return x * y
def div(x, y): return x / y
def pow(x, y): return np.abs(x)**y
def log(x): return np.log(x)
def inv(x): return np.reciprocal(x)

## ATTENTION: WE CANNOT USE A FUNCTION WITH A NAME STARTING WITH 'x'
FUNCTIONS = [add, sub, mul, div, pow, inv]
ARITY = defaultdict(int)
ARITY.update({'add' : 2, 'sub' : 2, 'mul' : 2, 'div' : 2, 'pow' : 2, 'log' : 1, 'inv' : 1})
INLINE = {'add' : ' + ', 'sub' : ' - ', 'mul' : ' * ', 'div' : ' / ', 'pow' : '**', 'inv' : '1/'}
TERMINALS = ['x0', 'p']

derivative = {'log' : lambda x: 1/x, 'exp' : lambda x: np.exp(x), 'inv' : lambda x: -1/(x**2)}
def deriveOP(op, l, diffL, r, diffR):
    if op == 'add':
        return diffL + diffR
    elif op == 'sub':
        return diffL - diffR
    elif op == 'mul':
        return diffL * r + diffR * l
    elif op == 'div':
        return (diffL * r - l * diffR) / (r**2)
    elif op == 'pow':
        return np.abs(l) ** r * (diffR * np.log(np.abs(l)) + (r * diffL)/l)

class GPTree:
    def __init__(self, data = None, left = None, right = None):
        self.data  = data
        self.val   = rng.uniform(-1, 1)
        self.left  = left
        self.right = right

    def node_label(self): # string label
        if (self.data in FUNCTIONS):
            return self.data.__name__
        else:
            return str(self.data)

    def print_expr(self, prefix = "", suffix = ""):
        arity = ARITY[self.node_label()]
        if arity == 2:
            print(prefix, end="")
            if self.node_label() == "pow":
                self.left.print_expr("abs(", ")")
            else:
                self.left.print_expr("(", ")")
            print(f"{INLINE[self.node_label()]}", end="")
            self.right.print_expr("(", ")")
            print(suffix, end="")
        elif arity == 1:
            print(prefix, end="")
            if self.node_label() == "inv":
                self.left.print_expr("1/(", ")")
            else:
                print(f"{self.node_label()}", end="")
                self.left.print_expr("(",")")
            print(suffix, end="")
        else:
            if self.node_label()[0] == 'x':
                print(f"{prefix}{self.node_label()}{suffix}", end="")
            else:
                print(f"{prefix}{self.val}{suffix}", end="")

    def num_params(self):
        if self.data == 'p': return 1
        elif self.node_label()[0] == 'x': return 0
        else:
            c = self.left.num_params()
            if ARITY[self.node_label()] == 2:
                c = c + self.right.num_params()
            return c

    def get_params(self):
        if self.data == 'p': return [self.val]
        elif self.node_label()[0] == 'x': return []
        else:
            c = self.left.get_params()
            if ARITY[self.node_label()] == 2:
                c = c + self.right.get_params()
            return c

    def set_params(self, t):
        if self.data == 'p':
            self.val = t[0]
            return t[1:]
        elif self.node_label()[0] == 'x': return t
        else:
            t = self.left.set_params(t)
            if ARITY[self.node_label()] == 2:
                t= self.right.set_params(t)
            return t

    def compute_tree(self, x, p):
        arity = ARITY[self.node_label()]
        if arity == 2:
            l, p = self.left.compute_tree(x, p)
            r, p = self.right.compute_tree(x, p)
            return self.data(l, r), p
        elif arity == 1:
            l, p = self.left.compute_tree(x, p)
            return self.data(l), p
        elif self.node_label()[0] == 'x':
            if len(x.shape) == 1:
                return x, p
            else:
                return x[int(self.node_label()[1:])], p
        elif self.data == 'p': return (p[0], p[1:])
        else: return (self.data, p)

    def compute_tree_diff(self, x, p): # TODO: autodiff
        arity = ARITY[self.node_label()]
        if arity == 2:
            l, p, diffL = self.left.compute_tree_diff(x, p)
            r, p, diffR = self.right.compute_tree_diff(x, p)
            return self.data(l, r), p, deriveOP(self.node_label(), l, diffL, r, diffR)
        elif arity == 1:
            l, p, diff = self.left.compute_tree_diff(x, p)
            return self.data(l), p, diff * derivative(self.node_label())(l)
        elif self.data[0] == 'x':
            if len(x.shape) == 1:
                return x, p, np.ones(x.shape[0])
            else:
                ix = int(self.node_label()[1:])
                diff = np.zeros(x.shape)
                diff[:, ix] = np.ones(x.shape[0])
                return x[ix], p, diff
        elif self.data == 'p':
            if len(x.shape) == 1:
                return (p[0], p[1:], np.zeros(x.shape[0]))
            else:
                return (p[0], p[1:], np.zeros(x.shape))
        else: return (self.data, p, np.zeros(x.shape))

    def random_tree(self, grow, max_depth, depth = 0, size = 1): # create random tree using either grow or full method
        if (depth < MIN_DEPTH or (depth < max_depth and not grow)) and (size <= MAX_SIZE - 2):
            self.data = FUNCTIONS[rng.integers(0, len(FUNCTIONS))]
        elif depth >= max_depth or size > MAX_SIZE - 2:
            self.data = TERMINALS[rng.integers(0, len(TERMINALS))]
        else: # intermediate depth, grow
            if rng.uniform() > 0.5:
                self.data = TERMINALS[rng.integers(0, len(TERMINALS))]
            else:
                self.data = FUNCTIONS[rng.integers(0, len(FUNCTIONS))]
        if self.data in FUNCTIONS:
            self.left = GPTree()
            arity2 = 1 if ARITY[self.node_label()] == 2 else 0
            self.left.random_tree(grow, max_depth, depth = depth + 1, size = size + 1 + arity2)
            sz_lft = self.left.size()
            if ARITY[self.node_label()] == 2:
                self.right = GPTree()
                self.right.random_tree(grow, max_depth, depth = depth + 1, size = size + sz_lft + 1)

    def mutation(self):
        if rng.random() < PROB_MUTATION:
            nodes = self.size()
            ix = rng.choice(nodes)
            self.mutate(ix, nodes, 0)
    def mutate(self, ix, max_nodes, d):
        if ix == 0:
            nodes = self.size()
            self.left = None
            self.right = None
            self.random_tree(grow = True, max_depth=MAX_DEPTH, depth=d, size=max_nodes-nodes+1)
            return ix-1
        else:
            if self.left:
                ix = self.mutate(ix-1, max_nodes, d+1)
            if ix > 0 and self.right:
                ix = self.mutate(ix-1, max_nodes, d+1)
            return ix

    def size(self): # tree size in nodes
        if self.data in TERMINALS: return 1
        l = self.left.size()  if self.left  else 0
        r = self.right.size() if self.right else 0
        return 1 + l + r

    def depth(self): # tree size in nodes
        if self.data in TERMINALS: return 1
        l = self.left.depth()  if self.left  else 0
        r = self.right.depth() if self.right else 0
        return max(l, r) + 1

    def build_subtree(self): # count is list in order to pass "by reference"
        t = GPTree()
        t.data = self.data
        if self.left:  t.left  = self.left.build_subtree()
        if self.right: t.right = self.right.build_subtree()
        return t

    def scan_tree(self, count, second, max_size = 0): # note: count is list, so it's passed "by reference"
        count[0] -= 1
        if count[0] <= 1:
            if not second: # return subtree rooted here
                return self.build_subtree()
            else: # glue subtree here
                self.data  = second.data
                self.left  = second.left
                self.right = second.right
        else:
            ret = None
            if self.left  and self.left.size() >= max_size: ret = self.left.scan_tree(count, second, max_size)
            if self.right and self.right.size() >= max_size: ret = self.right.scan_tree(count, second, max_size)
            return ret

    def crossover(self, other): # xo 2 trees at random nodes
        if rng.random() < XO_RATE:
            second = other.scan_tree([rng.integers(1, other.size()+1)], None) # 2nd random subtree
            if second.size() == MAX_SIZE:
                self = second.build_subtree()
            else:
                ix_max = int((MAX_SIZE - second.size() + 1)/2) - 1
                r = rng.integers(1, ix_max+1) if ix_max > 0 else 1
                self.scan_tree([r], second, second.size()) # 2nd subtree "glued" inside 1st tree

# end class GPTree

def init_population(ds): # ramped half-and-half
    pop = []
    fits = []
    for md in range(3, MAX_DEPTH + 1):
        grow = True
        for _ in range(int(POP_SIZE/(MAX_DEPTH - 3 + 1))):
            f = -np.inf
            while f == -np.inf:
                t = GPTree()
                t.random_tree(grow = grow, max_depth = md)
                f = fitness(t, ds)
            pop.append(t)
            fits.append(f)
            grow = not grow
    return pop, fits

def optimize(individual, ds):
    t0 = individual.get_params()
    if len(t0) == 0:
        return []

    def fun(theta):
        yhat = individual.compute_tree(ds[:,0], theta)[0]
        return np.mean((yhat-ds[:,-1])**2)

    sol = minimize(fun, t0, options = {'maxiter' : 10})
    individual.set_params(sol.x)
    print("NIT: ", sol.nit)
    return sol.x

def fitness(individual, ds):
    def fun(theta):
        yhat = individual.compute_tree(ds[:,0], theta)[0]
        return np.mean((yhat-ds[:,-1])**2)

    if individual.size() > MAX_SIZE:
        return -np.inf
    #t = optimize(individual, ds)
    t = individual.get_params()
    yhat = individual.compute_tree(ds[:,0], t)[0]
    neg_mse = -np.mean((yhat - ds[:,-1])**2)
    j = approx_fprime(t, fun)
    print(j)

    if np.isnan(neg_mse):
        return -np.inf
    else:
        return neg_mse

def selection(population, fitnesses): # select one individual using tournament selection
    tournament = [rng.integers(0, len(population))
                  for i in range(TOURNAMENT_SIZE)]
    tournament_fitnesses = [fitnesses[tournament[i]]
                            for i in range(TOURNAMENT_SIZE)
                            ]
    maxfit = max(tournament_fitnesses)
    champions = [tournament[i]
                 for i in range(TOURNAMENT_SIZE)
                 if tournament_fitnesses[i] == maxfit]
    if len(champions) == 1:
        return deepcopy(population[champions[0]])
    else:
        return deepcopy(population[champions[rng.integers(0, len(champions))]])

def evolve(population, fitnesses, gen):
    #parent1 = selection(population, fitnesses)
    #parent2 = selection(population, fitnesses)
    #parent1.crossover(parent2)
    #parent1.mutation()

    #if parent1.size() > MAX_SIZE:
    #    return evolve(population, fitnesses, gen)
    #return parent1
    t = GPTree()
    t.random_tree(grow = True, max_depth = MAX_DEPTH)

    return t

def report(population, fitnesses, ds, gen):
    for i, ind in enumerate(population):
        print(f"{gen},{i},", end="")
        ind.print_expr()
        print(f",{fitnesses[i]},{ind.size()}")

def main():
    #dataset = generate_dataset()
    dataset = pd.read_csv("nikuradse_2.csv").values
    population, fitnesses = init_population(dataset)
    #fitnesses = [fitness(individual, dataset) for individual in population]
    best_of_run_f = max(fitnesses)
    best_of_run = deepcopy(population[fitnesses.index(max(fitnesses))])
    best_of_run_gen = 0

    print("generation,individual_index,expression,fitness,nodes")

    # go evolution!
    for gen in range(GENERATIONS):
        report(population, fitnesses, dataset, gen)
        population = [evolve(population, fitnesses, gen) for _ in range(POP_SIZE-1)]
        fitnesses = [fitness(individual, dataset) for individual in population]
        # elitism implement
        if max(fitnesses) > best_of_run_f:
            best_of_run_f = max(fitnesses)
            best_of_run_gen = gen
            best_of_run = deepcopy(population[fitnesses.index(max(fitnesses))])
        else:
            #worst = min(enumerate(fitnesses), key = lambda x: x[1])[0]
            population.append(deepcopy(best_of_run))
            fitnesses.append(best_of_run_f)

    report(population, fitnesses, dataset, gen)

if __name__== "__main__":
  main()
