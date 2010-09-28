{- Copyright (c) 2010, Gregory M. Crosswhite. All rights reserved. -}

{-# LANGUAGE Rank2Types #-}

module TypeLevel.NaturalNumber.Induction where

import Control.Applicative
import Data.Functor.Identity
import TypeLevel.NaturalNumber

class Induction n where
    deductionM :: Monad m => a -> (f Zero -> a -> m b) -> (forall n. f (SuccessorTo n) -> a -> m (f n,a)) -> f n -> m b
    deduction2M :: Monad m => a -> (f Zero -> f Zero -> a -> m b) -> (forall n. f (SuccessorTo n) -> f (SuccessorTo n) -> a -> m (f n,f n,a)) -> f n -> f n -> m b
    inductionM :: Monad m => (a -> m (a,f Zero)) -> (forall n. a -> f n -> m (a,f (SuccessorTo n))) -> a -> m (a,f n)
    transformM :: Monad m => (f Zero -> m (g Zero)) -> (forall n. (f n -> m (g n)) -> f (SuccessorTo n) -> m (g (SuccessorTo n))) -> f n -> m (g n)

instance Induction Zero where
    deductionM a z _ b = z b a
    deduction2M a z _ b1 b2 = z b1 b2 a
    inductionM z _ a = z a
    transformM z _ = z

instance Induction n => Induction (SuccessorTo n) where
    deductionM a z d b = d b a >>= \(b',a') -> deductionM a' z d b'
    deduction2M a z d b1 b2 = d b1 b2 a >>= \(b'1,b'2,a') -> deduction2M a' z d b'1 b'2
    inductionM z i a = inductionM z i a >>= \(a',b') -> i a' b'
    transformM z i = i (transformM z i)

deduction :: Induction n => a -> (f Zero -> a -> b) -> (forall n. f (SuccessorTo n) -> a -> (f n,a)) -> f n -> b
deduction a z d b = runIdentity (deductionM a (\b a -> Identity (z b a)) (\b a -> Identity (d b a)) b)

deduction2 :: Induction n => a -> (f Zero -> f Zero -> a -> b) -> (forall n. f (SuccessorTo n) -> f (SuccessorTo n) -> a -> (f n,f n,a)) -> f n -> f n -> b
deduction2 a z d b1 b2 = runIdentity (deduction2M a (\b1 b2 a -> Identity (z b1 b2 a)) (\b1 b2 a -> Identity (d b1 b2 a)) b1 b2)

induction :: Induction n => (a -> (a,f Zero)) -> (forall n. a -> f n -> (a,f (SuccessorTo n))) -> a -> (a,f n)
induction z i a = runIdentity (inductionM (Identity . z) (\a b -> Identity (i a b)) a)

transform :: Induction n => (f Zero -> g Zero) -> (forall n. (f n -> g n) -> f (SuccessorTo n) -> g (SuccessorTo n)) -> f n -> g n
transform z i x = runIdentity (transformM (Identity . z) (\f -> Identity . i (runIdentity . f)) x)

inductionOnLeftFold :: Induction n => f Zero -> (forall n. a -> f n -> f (SuccessorTo n)) -> [a] -> f n
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

inductionOnRightFold :: Induction n => f Zero -> (forall n. a -> f n -> f (SuccessorTo n)) -> [a] -> f n
inductionOnRightFold z i = inductionOnLeftFold z i . reverse


inductionMOnLeftFold :: (Induction n, Monad m) => m (f Zero) -> (forall n. a -> f n -> m (f (SuccessorTo n))) -> [a] -> m (f n)
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

inductionMOnRightFold :: (Induction n, Monad m) => m (f Zero) -> (forall n. a -> f n -> m (f (SuccessorTo n))) -> [a] -> m (f n)
inductionMOnRightFold z i = inductionMOnLeftFold z i . reverse
