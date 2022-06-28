{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | This module introduces a type @'Ann' a@ to annotate data types with
-- information which doesn't influence the behaviour of your program. These
-- annotations can then be displayed, as assistance to the user.
--
-- = Examples
--
-- == Variable names
--
-- You are writing a programing language, and representing binder as [de Bruijn
-- indices](https://en.wikipedia.org/wiki/De_Bruijn_index). Nevertheless you
-- want to keep the variable names written by the user, to be able to interact
-- with them on these terms (/e.g./ in error messages). With 'Ann' it would look
-- like this:
--
-- > data Term
-- >   = Var Int
-- >   | App Term Term
-- >   | Lam (Ann String) Term
-- >   deriving (Eq)
--
-- Thanks to the 'Ann' type, you can derive the intended equality: the user's
-- choice of variable doesn't change the term (this is called α-equivalence).
--
-- == Validation monad
--
-- The [Validation](https://hackage.haskell.org/package/validation) applicative
-- can be made into a monad. Specifically @Validation (Ann e)@ is a monad, as I
-- explained [in a Twitter
-- thread](https://twitter.com/aspiwack/status/1511987089562341377).
--
-- = __Theoretical considerations__
--
-- @'Ann' a@ is the
-- [quotient](https://en.wikipedia.org/wiki/Equivalence_class#quotient_set) of
-- @a@ by the total relation.
--
-- == What's so special about the total relation?
--
-- There are only two relations which can be defined generically on all sets:
-- the empty relation and the total relation (this can be proved by
-- parametricity). The quotient by the empty relation is 'Identity'. So the only
-- interesting generic quotient is 'Ann'.
--
-- Strictly speaking, sets are also equipped with the equality relation (and you
-- can derive the disequality relation from it). But quotienting by the equality
-- relation is the same as quotienting by the empty relation; and quotienting by
-- the disequality relation is the same as quotienting by the total relation.
--
-- Other quotients can be defined on individual sets using abstract types.
--
-- A consequence of defining 'Ann' generically on types is that it turns 'Ann'
-- into a functor. The functor structure is not particularly intersting. But
-- 'Ann' is also a monad.
--
-- > (>>=) :: Ann a -> (a -> Ann b) -> Ann b
--
-- That is: you are allowed to “look inside” an @'Ann' a@ only if you you are
-- producing an @'Ann' b@ to begin with. The program is not allowed to depend on
-- the choice of representative, yet @(>>=)@ gives the representative for us to
-- play with. But it's alright: it's only going to affect the representative in
-- @'Ann' b@, on which the program cannot depend either.
--
-- Something that I'd like to point out is that you really need the @a@ in the
-- @(a -> Ann b)@ argument. The reason is that 'Ann' is not isomorphic to @Const
-- ()@: @'Ann' b@ is isomorphic to @()@ if and only if @b@ is inhabited. @'Ann'
-- Void@, on the other hand, is isomorphic to @Void@. There is a sense in which
-- all that's interesting about 'Ann' stems from this fact.
--
-- The monadic @(>>=)@ is more or less explicitly in use in many dependently
-- typed theories (it is pretty hidden, but there in the typing rules for @Prop@
-- in Coq). For further reading see [Propositions as
-- [Types] ](https://ieeexplore.ieee.org/abstract/document/8133549) and
-- [Implicit and noncomputational arguments using
-- monads](https://hal.archives-ouvertes.fr/hal-00150900/).
--
-- === Algebras of 'Ann'
--
-- I haven't talked about @return@ yet
--
-- > 'return' :: a -> Ann a
--
-- It is the canonical projection to @'Ann' a@. It's exported as 'project' as
-- well.
--
-- This is really not relevant for the design or usage of the library, but it's
-- a natural question to ask: the algebras of 'Ann' (as a monad) are sets with
-- at most 1 element. Let @α :: Ann A -> A@ be such an algebra. Since @Ann A@
-- has at most one element, @α@ is constant. But, by the laws of algebra, we
-- also have @α ∘ return = id@, in particular @id :: A -> A@ is constant,
-- therefore @A@ has at most 1 element.
--
-- Conversely, if @A@ has at most 1 element, then @'Ann' A@ is isomorphic to
-- @A@, in particular @A@ is an algebra.
--
-- === Is there an equivalent for subsets?
--
-- Frankly at this point, this is just me rambling about stuff that I find
-- interesting. I'll get back to relevant stuff in the next section.
--
-- Subsets are the dual of quotients (in category-theory terms, quotients are
-- co-equalisers while subsets are equalisers). However, the category of set is
-- not its own dual, so that there is an interesting phenomenon for one doesn't
-- imply that there is to the other.
--
-- In the case at hand, there are two generically definable predicates as
-- well. The empty predicate and the full predicate. They both define boring
-- subset (the empty set, and the identity functor, respectively). So really,
-- 'Ann' is the only interesting case of the bunch.
--
-- == Extracting and IO
--
-- The type of 'extract' is
--
-- > extract :: Ann a -> IO a
--
-- There can't be a function `Ann a -> a` as this violates the quotient
-- condition (concretely that the program isn't affected by the choice of
-- representative of 'Ann a'). Well, more precisely, if such a function exists,
-- it must be constant. The existence of such a function is a form of choice (of
-- the axiom of choice fame). It's a very powerful principle, and probably not
-- desirable. I should give a citation here, but no source comes to mind at the
-- moment. You will have to trust me that in dependently typed language, this
-- is equivalent to choice (in particular it implies the excluded middle, if
-- 'Ann a' is used to represent propositions).
--
-- Ok, back to 'IO'. We don't want the choice of representative to affect the
-- semantics of the program, but we still want to print it out, so that the user
-- get their debug message or whatnot. 'IO' is our solution because it is
-- allowed to do non-deterministic actions in 'IO' (and printing usually
-- involves 'IO', so it doesn't cost much). So the semantics of extract is
-- “choose an arbitrary representative“; this representative need not be the
-- same each time. Of course we don't actually want an arbitrary representative
-- to be printed out: we want the one we put in. It would be difficult to give a
-- different implementation anyway. So we know, that, really, we will get the
-- representative we put in. But, strictly speaking, this is not, strictly
-- speaking, part of the semantics of the function (at least I don't know how to
-- make it so; it would be really nice to be able to).
--
-- This same trick is used in [Tackling the awkward
-- squad](https://simon.peytonjones.org/Tackling-the-awkward-squad/).
--
-- == Quotients and equivalence relations
--
-- This is even less related to the core of the package than the rest of this
-- section, but while we are on the subject of quotients, I'd like to address a
-- point.
--
-- You may have noticed that I repeatedly spoke of quotienting by “a relation”
-- throughout this document. If you are like me, though, you may have been
-- taught that a set is quotiented by an /equivalence relation/. It's because
-- equivalence classes form an equivalence relation. But it isn't essential to
-- the definition of quotient.
--
-- A quotient \(X/R\) of a set \(X\) is defined by its universal
-- property. Namely that a function \(f \in X/R \rightarrow C\)` is the same
-- thing as a function \(f' \in X \rightarrow C\) such that
-- \(x R y \Longrightarrow f x = f y\). That \(R\) is an equivalence relation doesn't
-- play a role in this definition. It turns out, however, that quotienting by
-- \(R\) or by its reflexive, symmetric and transitive closure yields the same
-- set.


module Data.Ann
  ( Ann,
    project,
    extract,
    unsafeExtract,
  )
where

import Data.Functor.Identity

-- | @'Ann' a@ is the type of annotations of type @a@. It is such, in particular
-- that, for all @x :: 'Ann' a@ and @y :: 'Ann' a@, @x == y@.
newtype Ann a = Squash a
  deriving
    (Semigroup, Monoid, Read, Show)
    via (Identity a)

-- | See @Monad@ instance
deriving via Identity instance Functor Ann
-- | See @Monad@ instance
deriving via Identity instance Applicative Ann
-- | The particular choice of annotation may not affect the meaning of the
-- program. One way to prove to Haskell that you can safely depend on the
-- underlying annotation is to use it only to build an @'Ann' b@. The monad
-- instance gives you this ability. More (too much?) detail in the theoretical
-- considerations.
deriving via Identity instance Monad Ann

instance Eq (Ann a) where
  _ == _ = True

instance Ord (Ann a) where
  _ <= _ = True
  compare _ _ = EQ

-- | When all else fails – if neither the @Monad@ instance nor 'extract' fit
-- your need – you can use 'unsafeExtract' to observe the underlying value of an
-- annotation.
--
-- ⚠️ You /must/ prove that you are not using @'unsafeExtract ann@ in a way where
-- changing the value of @ann@ would change the behaviour of your program.
unsafeExtract :: Ann a -> a
unsafeExtract (Squash a) = a

-- | Extract the underlying value of an annotation. We have that @extract
-- . project = return@. But do keep in mind that valid refactoring can change
-- the underlying value of the annotation. As such, 'extract' is a
-- non-deterministic operation.
extract :: Ann a -> IO a
extract = return . unsafeExtract

-- | Create an annotation. See also 'extract'.
project :: a -> Ann a
project = Squash
