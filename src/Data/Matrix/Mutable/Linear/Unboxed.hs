{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Data.Matrix.Mutable.Linear.Unboxed (
  Matrix (),
  emptyL,
  fromRowL,
  fromRowsL,
  numRows,
  numEntries,
  pushRow,
  getRow,
  unsafeGetRow,
  getEntry,
  unsafeGetEntry,
  popRow,
  dropRowsEnd,
  shrinkToFit,
) where

import qualified Control.Functor.Linear as C
import Data.Alloc.Linearly.Token (Linearly, besides)
import qualified Data.Array.Polarized as PV
import qualified Data.Array.Polarized.Pull.Extra as Pull
import qualified Data.Array.Polarized.Push.Extra as Push
import qualified Data.List as List
import qualified Data.Unrestricted.Linear as Ur
import qualified Data.Vector.Mutable.Linear.Unboxed as LUV
import qualified Data.Vector.Unboxed as U
import GHC.Stack (HasCallStack)
import Prelude.Linear
import qualified Prelude as P

data Matrix a where
  Matrix ::
    {-# UNPACK #-} !(LUV.Vector Int) %1 ->
    !(LUV.Vector a) %1 ->
    Matrix a

instance Consumable (Matrix a) where
  consume (Matrix c p) = c `lseq` consume p
  {-# INLINE consume #-}

{- HLINT ignore module "Use bimap" -}
instance (U.Unbox a) => Dupable (Matrix a) where
  {-# INLINE dup2 #-}
  dup2 (Matrix c p) =
    dup2 c & \(c, c') ->
      dup2 p & \(p, p') ->
        (Matrix c p, Matrix c' p')

emptyL :: (U.Unbox a) => Linearly %1 -> Matrix a
{-# INLINE emptyL #-}
emptyL l =
  besides l (\l -> LUV.constantL l 1 0) & \(offsets, l) ->
    LUV.emptyL l & Matrix offsets

fromRowL :: (U.Unbox a) => Linearly %1 -> U.Vector a %1 -> Matrix a
{-# INLINE fromRowL #-}
fromRowL l uv =
  besides l (`LUV.fromVectorL` uv) & \(payload, l) ->
    LUV.size payload & \(Ur sz, payload) ->
      LUV.fromListL l [0, sz] & \offsets -> Matrix offsets payload

fromRowsL :: (U.Unbox a) => Linearly %1 -> [U.Vector a] -> Matrix a
{-# INLINE fromRowsL #-}
fromRowsL l rows =
  besides
    l
    (`LUV.fromListL` List.scanl' (flip $ (P.+) P.. U.length) 0 rows)
    & \(offs, l) ->
      Matrix offs
        $ LUV.fromVectorL l
        $ Push.alloc
        $ foldMap' (PV.transfer . Pull.fromVector) rows

numRows :: Matrix a %1 -> (Ur Int, Matrix a)
{-# INLINE numRows #-}
numRows (Matrix offsets payload) =
  LUV.size offsets & \(Ur offSz, offsets) ->
    (Ur (offSz - 1), Matrix offsets payload)

numEntries :: Matrix a %1 -> (Ur Int, Matrix a)
{-# INLINE numEntries #-}
numEntries (Matrix offsets payload) =
  LUV.size payload & \(Ur len, payload) ->
    (Ur len, Matrix offsets payload)

pushRow :: (U.Unbox a) => U.Vector a -> Matrix a %1 -> Matrix a
{-# INLINE pushRow #-}
pushRow uv mat =
  numEntries mat & \(Ur oldOffs, Matrix offsets payload) ->
    Matrix
      (LUV.push (U.length uv + oldOffs) offsets)
      (LUV.appendVector uv payload)

-- | Pop the last row of the matrix. This will never shrink the vector, use shrinkToFit to remove the wasted space.
popRow :: (U.Unbox a) => Matrix a %1 -> (Ur (Maybe (U.Vector a)), Matrix a)
popRow mat =
  numEntries mat & \(Ur origEnts, Matrix offs ents) ->
    LUV.pop offs & \(Ur mlen, offs) ->
      mlen & \case
        Nothing -> (Ur Nothing, Matrix offs ents)
        Just len ->
          LUV.unsafeSlice' (origEnts - len) len ents & \(ents, popped) ->
            (Ur.lift Just (LUV.freeze popped), Matrix offs ents)

-- |  Retrievies a row copying.
unsafeGetRow :: (U.Unbox a) => Int -> Matrix a %1 -> (Ur (U.Vector a), Matrix a)
{-# INLINE unsafeGetRow #-}
unsafeGetRow i (Matrix offs ents) =
  LUV.unsafeGet i offs & \(Ur start, offs) ->
    LUV.unsafeGet (i + 1) offs & \(Ur end, offs) ->
      LUV.unsafeSlice' start (end - start) ents & \(ents, uvSeed) ->
        (LUV.freeze uvSeed, Matrix offs ents)

getRow :: (HasCallStack, U.Unbox a) => Int -> Matrix a %1 -> (Ur (U.Vector a), Matrix a)
{-# INLINE getRow #-}
getRow i mat =
  numRows mat & \(Ur n, mat) ->
    (0 <= i && i < n) & \case
      True -> unsafeGetRow i mat
      False -> error ("getRow: row index out of bound: " <> show (i, n)) mat

unsafeGetEntry :: (U.Unbox a) => Int -> Int -> Matrix a %1 -> (Ur a, Matrix a)
{-# INLINE unsafeGetEntry #-}
unsafeGetEntry i j (Matrix offs ents) =
  LUV.unsafeGet i offs & \(Ur start, offs) ->
    C.fmap (Matrix offs) (LUV.unsafeGet (start + j) ents)

getEntry :: (HasCallStack, U.Unbox a) => Int -> Int -> Matrix a %1 -> (Ur a, Matrix a)
{-# INLINE getEntry #-}
getEntry i j mat =
  numRows mat & \(Ur rowCount, Matrix offs ents) ->
    i >= rowCount & \case
      True ->
        offs
          `lseq` ents
          `lseq` error ("getEntry: row index out of bound: " <> show (i, rowCount))
      False ->
        LUV.unsafeGet i offs & \(Ur off, offs) ->
          LUV.unsafeGet (i + 1) offs & \(Ur end, offs) ->
            let len = end - off
             in j >= len & \case
                  True ->
                    offs
                      `lseq` ents
                      `lseq` error ("getEntry: column index out of bound: " <> show (j, len))
                  False -> unsafeGetEntry i j (Matrix offs ents)

-- | shrinkToFit
shrinkToFit :: (U.Unbox a) => Matrix a %1 -> Matrix a
shrinkToFit (Matrix off pay) = Matrix (LUV.shrinkToFit off) (LUV.shrinkToFit pay)

dropRowsEnd :: (U.Unbox a) => Int -> Matrix a %1 -> Matrix a
{-# INLINE dropRowsEnd #-}
dropRowsEnd n mat =
  numRows mat & \(Ur nrows, Matrix offs ents) ->
    n >= nrows & \case
      True -> Matrix (LUV.unsafeSlice 0 0 offs) (LUV.unsafeSlice 0 0 ents)
      False ->
        LUV.unsafeGet n offs & \(Ur k, offs) ->
          Matrix (LUV.unsafeSlice 0 n offs) (LUV.unsafeSlice 0 k ents)
