{- Copyright (c) 2010, Gregory M. Crosswhite. All rights reserved. -}

{-# LANGUAGE Rank2Types #-}

module TypeLevel.NaturalNumber.Induction (
    -- * Monadic interface
    Induction(..),
    inductionMOnLeftFold,
    inductionMOnRightFold,
    -- * Pure (non-monadic) interface
    deduction,
    deduction2,
    induction,
    transform,
    inductionOnLeftFold,
    inductionOnRightFold,
) where

import Control.Applicative
import Data.Functor.Identity
import TypeLevel.NaturalNumber

-- | The Induction class contains high-level combinators for
-- performing monadic operations on inductive structures --- that is,
-- datatypes tagged with a natural number.
class Induction n where
    -- | The 'deductionM' method provides a high-level combinator for
    -- folding monadically over an inductive structure; essentially
    -- this method is the opposite of the 'inductionM' method which
    -- builds up an inductive structure rather than tearing one down.
    -- See 'deduction' for a non-monadic version of this function, and
    -- 'deduction2M' for a version of this function acting on two
    -- structures simultaneously rather than one.
    deductionM ::
        Monad m
        => α                                                -- ^ the seed data
        -> (f Zero -> α -> m β)                             -- ^ the action to perform for the base case
        -> (forall n. f (SuccessorTo n) -> α -> m (f n,α))  -- ^ the action to perform for the inductive case
        -> f n                                              -- ^ the structure to fold over
        -> m β                                              -- ^ the (monadic) result

    -- | The 'deduction2M' method is the same idea as the 'deductionM'
    -- method, but it simultaneously folds over two inductive structures
    -- rather than one.
    deduction2M ::
        Monad m
        => α                                                                        -- ^ the seed data
        -> (f Zero -> g Zero -> α -> m β)                                           -- ^ the action to perform for the base case
        -> (forall n. f (SuccessorTo n) -> g (SuccessorTo n) -> α -> m (f n,g n,α)) -- ^ the action to perform for the inductive case
        -> f n                                                                      -- ^ the first of the two structures to fold over
        -> g n                                                                      -- ^ the second of the two structures to fold over
        -> m β                                                                      -- ^ the (monadic) result

    -- | The 'inductionM' method provides a high-level combinator for
    -- building up an inductive structure monadically starting from
    -- given seed data; essentially this method is the opposite of
    -- `deductionM' method which tears down an inductive structure
    -- rather than building one up.  See 'induction' for a non-monadic
    -- version of this function.
    inductionM ::
        Monad m
        => (α -> m (α,f Zero))                             -- ^ the action to perform for the base case
        -> (forall n. α -> f n -> m (α,f (SuccessorTo n))) -- ^ the action to perform for the inductive case
        -> α                                               -- ^ the seed data for the operation
        -> m (α,f n)                                       -- ^ the (monadic) result

    -- | The 'transformM' method provides a high-level combinator for
    -- monadically transforming one inductive structure into another.
    -- See 'transform' for a non-monadic version of this function.
    transformM ::
        Monad m
        => (f Zero -> m (g Zero))                                                       -- ^ the action to perform for the base case
        -> (forall n. (f n -> m (g n)) -> f (SuccessorTo n) -> m (g (SuccessorTo n)))   -- ^ the action to perform for the inductive case
        -> f n                                                                          -- ^ the structure to be transformed
        -> m (g n)                                                                      -- ^ the (monadic) resulting transformed structure

instance Induction Zero where
    -- | Implementation of the Induction class for the base case.
    deductionM a z _ b = z b a
    deduction2M a z _ b1 b2 = z b1 b2 a
    inductionM z _ a = z a
    transformM z _ = z

instance Induction n => Induction (SuccessorTo n) where
    -- | Implementation of the Induction class for the inductive case.
    deductionM a z d b = d b a >>= \(b',a') -> deductionM a' z d b'
    deduction2M a z d b1 b2 = d b1 b2 a >>= \(b'1,b'2,a') -> deduction2M a' z d b'1 b'2
    inductionM z i a = inductionM z i a >>= \(a',b') -> i a' b'
    transformM z i = i (transformM z i)

-- | The 'deduction' function provides a high-level combinator for
-- folding over an inductive structure; essentially this method is the
-- opposite of the 'induction' method which builds up an inductive
-- structure rather than tearing one down.  See 'deductionM' for a
-- monadic version of this function, and 'deduction' for a version of
-- this function acting on two structures simultaneously rather than
-- one.
deduction ::
    Induction n
    => α                                              -- ^ the seed data
    -> (f Zero -> α -> β)                             -- ^ the base case
    -> (forall n. f (SuccessorTo n) -> α -> (f n,α))  -- ^ the inductive case
    -> f n                                            -- ^ the structure to fold over
    -> β                                              -- ^ the result
deduction a z d b = runIdentity (deductionM a (\b a -> Identity (z b a)) (\b a -> Identity (d b a)) b)

-- | The 'deduction2' function is the same idea as the 'deductionM'
-- function, but it simultaneously folds over two inductive structures
-- rather than one.
deduction2 ::
    Induction n
    => α                                                                        -- ^ the seed data
    -> (f Zero -> g Zero -> α -> β)                                             -- ^ the base case
    -> (forall n. f (SuccessorTo n) -> g (SuccessorTo n) -> α -> (f n,g n,α))   -- ^ the inductive case
    -> f n                                                                      -- ^ the first of the two structures to fold over
    -> g n                                                                      -- ^ the second of the two structures to fold over
    -> β                                                                        -- ^ the result
deduction2 a z d b1 b2 = runIdentity (deduction2M a (\b1 b2 a -> Identity (z b1 b2 a)) (\b1 b2 a -> Identity (d b1 b2 a)) b1 b2)

-- | The 'induction' function provides a high-level combinator for
-- building up an inductive structure starting from given seed data;
-- essentially this method is the opposite of `deduction' method which
-- tears down an inductive structure rather than building one up.  See
-- 'inductionM' for a monadic version of this function.
induction :: Induction n => (a -> (a,f Zero)) -> (forall n. a -> f n -> (a,f (SuccessorTo n))) -> a -> (a,f n)
induction z i a = runIdentity (inductionM (Identity . z) (\a b -> Identity (i a b)) a)

-- | The 'transform' function provides a high-level combinator for
-- transforming one inductive structure into another.  See
-- 'transformM' for a monadic version of this function.
transform :: Induction n => (f Zero -> g Zero) -> (forall n. (f n -> g n) -> f (SuccessorTo n) -> g (SuccessorTo n)) -> f n -> g n
transform z i x = runIdentity (transformM (Identity . z) (\f -> Identity . i (runIdentity . f)) x)

-- | The 'inductionOnLeftFold' function is provided for the common
-- case where one is building up an inductive structure by performing
-- a left fold over a list.  A pre-condition of calling this function
-- is that the list be the same size as the data structure, i.e. that
-- the length of the list be equal to the natural number tagging the
-- structure.  When this pre-condition is violated, it returns _|_ by
-- calling 'error' with a message that the list is either too long or
-- too short.  See 'inductionMOnLeftFold' for a monadic version of
-- this function, and 'inductionOnRightFold' for a version of this
-- function that performs a right fold over the list.
inductionOnLeftFold ::
    Induction n
    => f Zero                                    -- ^ the base case
    -> (forall n. α -> f n -> f (SuccessorTo n)) -- ^ the inductive case
    -> [α]                                       -- ^ the list to fold over
    -> f n                                       -- ^ the result
inductionOnLeftFold z i list =
    case leftovers of
        [] -> final
        _ -> error "List is too long."
  where
    (leftovers,final) =
        induction
            (\l -> (l,z))
            (\l a ->
                 case l of
                     (x:xs) -> (xs,i x a)
                     _ -> error "List is too short."
            )
            list

-- | This function is the same idea as 'inductionOnLeftFold' function,
-- but it performs a right-fold rather than a left-fold over the list.
-- See 'inductionMOnRightFold' for a monadic version of this function.
inductionOnRightFold ::
    Induction n
    => f Zero                                    -- ^ the base case
    -> (forall n. α -> f n -> f (SuccessorTo n)) -- ^ the inductive case
    -> [α]                                       -- ^ the list to fold over
    -> f n                                       -- ^ the result
inductionOnRightFold z i = inductionOnLeftFold z i . reverse

-- | The 'inductionMOnLeftFold' function is provided for the common
-- case where one is building up an inductive structure by performing
-- a monadic left fold over a list.  A pre-condition of calling this
-- function is that the list be the same size as the data structure,
-- i.e. that the length of the list be equal to the natural number
-- tagging the structure.  When this pre-condition is violated, it
-- returns _|_ by calling 'error' with a message that the list is
-- either too long or too short.  See 'inductionOnLeftFold' for a
-- non-monadic version of this function, and 'inductionMOnRightFold'
-- for a version of this function that performs a right fold over the
-- list.
inductionMOnLeftFold ::
    (Induction n, Monad m)
    => m (f Zero)                                       -- ^ the action to perform for the base case
    -> (forall n. α -> f n -> m (f (SuccessorTo n)))    -- ^ the action to perform for the inductive case
    -> [α]                                              -- ^ the list to fold over
    -> m (f n)                                          -- ^ the (monadic) result
inductionMOnLeftFold z i list = do
    (leftovers,final) <-
        inductionM
            (\l -> z >>= \a' -> return (l,a'))
            (\l a ->
                 case l of
                     (x:xs) -> i x a >>= \a' -> return (xs,a')
                     _ -> error "List is too short."
            )
            list
    case leftovers of
        [] -> return final
        _ -> error "List is too long."

-- | This function is the same idea as 'inductionMOnLeftFold' function,
-- but it performs a right-fold rather than a left-fold over the list.
-- See 'inductionOnRightFold' for a non-monadic version of this function.
inductionMOnRightFold ::
    (Induction n, Monad m)
    => m (f Zero)                                       -- ^ the action to perform for the base case
    -> (forall n. α -> f n -> m (f (SuccessorTo n)))    -- ^ the action to perform for the inductive case
    -> [α]                                              -- ^ the list to fold over
    -> m (f n)                                          -- ^ the (monadic) result
inductionMOnRightFold z i = inductionMOnLeftFold z i . reverse
