# Ann

This package introduces a type `Ann a` to annotate data types with
information which doesn't influence the behaviour of your
program. These annotations can then be displayed, as assistance to the
user.

## Examples

### Variable names

You are writing a programing language, and representing binder as [de
Bruijn indices](https://en.wikipedia.org/wiki/
De_Bruijn_index). Nevertheless you want to keep the variable names
written by the user, to be able to interact with them on these terms
(_e.g._ in error messages). With 'Ann' it would look like this:

```haskell
data Term
  = Var Int
  | App Term Term
  | Lam (Ann String) Term
  deriving (Eq)
```

Thanks to the 'Ann' type, you can derive the intended equality: the
user's choice of variable doesn't change the term (this is called
α-equivalence).

### Validation monad

The [Validation](https://hackage.haskell.org/package/validation)
applicative can be made into a monad. Specifically `Validation (Ann
e)` is a monad, as I explained [in a Twitter
thread](https://twitter.com/aspiwack/status/1511987089562341377)
