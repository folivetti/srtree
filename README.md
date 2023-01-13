# srtree: A symbolic regression expression tree structure.

`srtree` is a Haskell library with a data structure and supporting functions to manipulate expression trees for symbolic regression.

The tree-like structure is parameterized by the type of the variables indexing and the return value when evaluating the tree. The most common is to index the variables with `Int` starting at $0$ and to return a `Double`. The Functor instance changes the type of the stored/returned values.

The tree supports leaf nodes containing a variable, a free parameter, or a constant value; internal nodes that represents binary operators such as the four basic math operations, logarithm with custom base, and the power of two expressions; and unary functions specified by `Function` data type.

This library also defines the `OptInt` class with the operator `^.` that represents the integral power. This is needed to automatically simplify some constructs of the tree and also when using interval arithmetic, that requires a special case of integral power.

The `SRTree` structure has instances for `Num, Fractional, Floating` which allows to create an expression as a valid Haskell expression such as:

```haskell
x = Var 0
y = Var 1
expr = x * 2 + sin(y * pi + x) :: SRTree Int Double
```

There is also a `Bifunctor` instance that allows to change the type of both parameters, and an `Applicative, Foldable, Traversable` instances. To traverse by the index type, there is a function called `traverseIx`.

## Other features:

- simplification algorithm (`simplify`)
- derivative w.r.t. a variable (`deriveBy`) and w.r.t. a parameter (`deriveParamBy`)
- evaluation (`evalTree`)
- relabel free parameters sequentially (`relabelParams`)
- relabel variables couting their occurrence (`relabelOccurrences`, used with interval arithmetic)

## TODO:

- support more advanced functions
- support conditional branching (`IF-THEN-ELSE`)

