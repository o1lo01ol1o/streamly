{-# LANGUAGE FlexibleContexts          #-}

-- |
-- Module      : Streamly.Streams.SVar
-- Copyright   : (c) 2017 Harendra Kumar
--
-- License     : BSD3
-- Maintainer  : harendra.kumar@gmail.com
-- Stability   : experimental
-- Portability : GHC
--
--
module Streamly.Streams.SVar
    ( fromSVar
    , toSVar
    )
where

import Control.Exception (fromException)
import Control.Monad (when)
import Control.Monad.Catch (throwM)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.IORef (newIORef, readIORef, mkWeakIORef, writeIORef)
import Data.Maybe (isNothing)
import Data.Semigroup ((<>))
import System.IO (hPutStrLn, stderr)
import Streamly.Time.Clock (Clock(Monotonic), getTime)
import System.Mem (performMajorGC)

import Streamly.SVar
import Streamly.Streams.StreamK hiding (reverse)

printSVar :: SVar t m a -> String -> IO ()
printSVar sv how = do
    svInfo <- dumpSVar sv
    hPutStrLn stderr $ "\n" <> how <> "\n" <> svInfo

-- | Pull a stream from an SVar.
{-# NOINLINE fromStreamVar #-}
fromStreamVar :: MonadAsync m => SVar Stream m a -> Stream m a
fromStreamVar sv = mkStream $ \st yld sng stp -> do
    list <- readOutputQ sv
    -- Reversing the output is important to guarantee that we process the
    -- outputs in the same order as they were generated by the constituent
    -- streams.
    foldStream st yld sng stp $ processEvents $ reverse list

    where

    allDone stp = do
        when (svarInspectMode sv) $ do
            t <- liftIO $ getTime Monotonic
            liftIO $ writeIORef (svarStopTime (svarStats sv)) (Just t)
            liftIO $ printSVar sv "SVar Done"
        stp

    {-# INLINE processEvents #-}
    processEvents [] = mkStream $ \st yld sng stp -> do
        done <- postProcess sv
        if done
        then allDone stp
        else foldStream st yld sng stp $ fromStreamVar sv

    processEvents (ev : es) = mkStream $ \st yld sng stp -> do
        let rest = processEvents es
        case ev of
            ChildYield a -> yld a rest
            ChildStop tid e -> do
                accountThread sv tid
                case e of
                    Nothing -> foldStream st yld sng stp rest
                    Just ex ->
                        case fromException ex of
                            Just ThreadAbort ->
                                foldStream st yld sng stp rest
                            Nothing -> liftIO (cleanupSVar sv) >> throwM ex

{-# INLINE fromSVar #-}
fromSVar :: (MonadAsync m, IsStream t) => SVar Stream m a -> t m a
fromSVar sv =
    mkStream $ \st yld sng stp -> do
        ref <- liftIO $ newIORef ()
        _ <- liftIO $ mkWeakIORef ref hook
        -- We pass a copy of sv to fromStreamVar, so that we know that it has
        -- no other references, when that copy gets garbage collected "ref"
        -- will get garbage collected and our hook will be called.
        foldStreamShared st yld sng stp $
            fromStream $ fromStreamVar sv{svarRef = Just ref}
    where

    hook = do
        when (svarInspectMode sv) $ do
            r <- liftIO $ readIORef (svarStopTime (svarStats sv))
            when (isNothing r) $
                printSVar sv "SVar Garbage Collected"
        cleanupSVar sv
        -- If there are any SVars referenced by this SVar a GC will prompt
        -- them to be cleaned up quickly.
        when (svarInspectMode sv) performMajorGC

-- | Write a stream to an 'SVar' in a non-blocking manner. The stream can then
-- be read back from the SVar using 'fromSVar'.
toSVar :: (IsStream t, MonadAsync m) => SVar Stream m a -> t m a -> m ()
toSVar sv m = toStreamVar sv (toStream m)
