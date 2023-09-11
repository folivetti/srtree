# srtree: A symbolic regression expression tree structure.

`srtree` is a Haskell library with a data structure and supporting functions to manipulate expression trees for symbolic regression.

The tree-like structure is defined as a fixed-point of an n-ary tree. The variables and parameters of the regression model are indexed as `Int`type and the constant values are `Double`.

The tree supports leaf nodes containing a variable, a free parameter, or a constant value; internal nodes that represents binary operators such as the four basic math operations, logarithm with custom base, and the power of two expressions; and unary functions specified by `Function` data type.

The `SRTree` structure has instances for `Num, Fractional, Floating` which allows to create an expression as a valid Haskell expression such as:

```haskell
x = var 0)
y = var 1
expr = x * 2 + sin(y * pi + x) :: Fix SRTree
```

## Other features:

- derivative w.r.t. a variable (`deriveByVar`) and w.r.t. a parameter (`deriveByParam`)
- evaluation (`evalTree`)
- relabel free parameters sequentially (`relabelParams`)
- gradient calculation with `forwardMode`, or optimized with `gradParams` if there is only a single occurrence of each parameter (most of the cases).

## TODO:

- support more advanced functions
- support conditional branching (`IF-THEN-ELSE`)

