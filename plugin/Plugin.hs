-- Run plugin with option `-fplugin=Plugin`, and build-depends on this
-- package `plugin`.
--
-- Plugin is currently very experimental and fragile, careless usage
-- can panic ghc and make the impossible happen.
--
-- Needless to mention that this plugin is also very buggy, and is
-- only a POC. One known case where it makes GHC panic is
-- `wordsUnwordsCopy` benchmarks in FileIO, there are probably many
-- other such ones.
--
-- This plugin inlines non recursive join points whose definition
-- begins with a case match on a type that is annotated with
-- MAKE_ME_GO_AWAY. When everything goes well, this can fuse and
-- completely eliminate intermediate constructors resulting in drastic
-- performance gains. Here are some major improvements on a 143MB file:
--
{-
| Benchmark Name                                    | Old    | New     |
|---------------------------------------------------+--------+---------|
| readStream/wordcount                              | 1.969s | 308.1ms |
| decode-encode/utf8-arrays                         | 4.159s | 2.952s  |
| decode-encode/utf8                                | 5.708s | 2.117s  |
| splitting/predicate/wordsBy isSpace (word count)  | 2.050s | 311.5ms |
| splitting/long-pattern/splitOnSuffixSeq abc...xyz | 2.558s | 423.3ms |
-}
--
-- The performance improvements suggest that this is something that
-- would be nice to further pursue with a more principled approach
-- than present here.
--
-- This plugin currently runs after the simplifier runs phase 0
-- followed by a gentle simplify that does both inlining, and
-- case-case twice and then runs the rest of the CoreToDos. This
-- inlining could further create a recursive join point that does an
-- explicit case match on a type that would benefit again from
-- inlining, so in the second run we should create a loop breaker and
-- transform the recursive join point to a non-recursive join point
-- and inline. This is not currently done, the machinery is already
-- available, just create a loop breaker for Let Rec in
-- `replaceBothBindAndCall`.

{-# LANGUAGE NoMonomorphismRestriction #-} -- Why did I enable this??
{-# LANGUAGE DeriveDataTypeable #-}

module Plugin (plugin, MAKE_ME_GO_AWAY(..)) where

import BasicTypes
import GhcPlugins hiding ((<>))
import SimplCore
import CoreMonad
import Unique

import Control.Monad (when)
import Data.Monoid (Any(..))
import Data.Generics.Schemes
import Data.Generics.Aliases

import qualified Data.List as DL
import Data.Data

import Data.Data

data MAKE_ME_GO_AWAY = MAKE_ME_GO_AWAY deriving Data

plugin :: Plugin
plugin =
    defaultPlugin {installCoreToDos = install}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo@(a:b:c:d:e:f:g:h:i:j:todos) = do
    dflags <- getDynFlags
    putMsgS "Hello!"
    putMsgS $ showSDoc dflags (ppr todo)
    let myplugin = CoreDoPluginPass "My Plugin" pass
        simplsimplify =
            CoreDoSimplify
                (maxSimplIterations dflags)
                SimplMode
                    { sm_phase = InitialPhase
                    , sm_names = ["Gentle"]
                    , sm_dflags = dflags
                    , sm_rules = gopt Opt_EnableRewriteRules dflags
                    , sm_eta_expand = gopt Opt_DoLambdaEtaExpansion dflags
                    , sm_inline = True
                    , sm_case_case = True
                    }
    -- We run our plugin once the simplifier finishes phase 0,
    -- followed by a gentle simplifier which inlines and case-cases
    -- twice. TODO: The gentle simplifier runs on the whole program,
    -- however it might be better to call `simplifyExpr` on the
    -- expression directly.
    --
    -- TODO: Do proper creation of CoreToDo's instead of this
    -- destructuring.

    return $ (a:b:c:d:e:f:myplugin:simplsimplify:myplugin:simplsimplify:g:h:i:j:todos)
    --return todo

pass :: ModGuts -> CoreM ModGuts
pass guts = do
    dflags <- getDynFlags
    anns <- getAnnotations deserializeWithData guts
    putMsgS "Begin Pass"
    a <- bindsOnlyPass (mapM (transformBind dflags anns)) guts
    putMsgS "End Pass"
    return a
  where
    transformBind ::
           DynFlags -> UniqFM [MAKE_ME_GO_AWAY] -> CoreBind -> CoreM CoreBind
    transformBind dflags anns bndr@(NonRec b expr) = do
        --putMsgS $ "binding named " ++ showSDoc dflags (ppr b)
        let lets = DL.nub $ letBndrsThatAreCases (altsContainsAnn anns) expr
        --putMsgS $ "Bndrs of required Case Alts\n" ++ showSDoc dflags (ppr lets)
        let expr' =
                DL.foldl'
                    (\e b ->
                         let b' = setAlwaysInlineOnBndr b
                          in replaceBind b b' e)
                    expr
                    lets
        return (NonRec b expr')
        --return bndr
    -- This is probably wrong, but we don't need it for now.
    transformBind dflags anns bndr@(Rec bs) = do
        --putMsgS "Pickle Rick:\n"
        --mapM_ (\(b, expr) -> transformBind dflags anns (NonRec b expr)) bs
        --putMsgS "Pickle Rick ends\n"
        return bndr

-- Checks whether a case alternative contains a type with the
-- annotation.  Only checks the first typed element in the list, so
-- only pass alternatives from one case expression.
altsContainsAnn :: UniqFM [MAKE_ME_GO_AWAY] -> [Alt CoreBndr] -> Bool
altsContainsAnn _ [] = False
altsContainsAnn anns ((DataAlt dcon, _, _):alts) =
    case lookupUFM anns (getUnique $ dataConTyCon dcon) of
        Nothing -> False
        Just _ -> True
altsContainsAnn anns ((DEFAULT, _, _):alts) = altsContainsAnn anns alts
altsContainsAnn _ _ = False

containsCase :: CoreExpr -> Bool
containsCase =
    getAny .
      everything
        (<>)
        (mkQ (Any False) matches)
  where
    matches :: CoreExpr -> Any
    matches (Case _ _ _ _) = Any True
    matches _ = Any False

-- returns the Bndrs, that are either of the form
-- joinrec { $w$g0 x y z = case y of predicateAlt -> ... } -> returns [$w$go]
-- join { $j1_sGH1 x y z = case y of predicateAlt -> ... } -> returns [$j1_sGH1]
--
-- Can check the call site and return only those that would enable
-- case-of-known constructor to kick in. Or is that not relevant?
-- This only concentrates on explicit Let's, doesn't care about top level
-- Case or Lam or App.
letBndrsThatAreCases :: ([Alt CoreBndr] -> Bool) -> CoreExpr -> [CoreBndr]
letBndrsThatAreCases pred expr = letBndrsThatAreCases' undefined False expr
  where
    letBndrsThatAreCases' :: CoreBndr -> Bool -> CoreExpr -> [CoreBndr]
    letBndrsThatAreCases' b _ (App expr1 expr2) =
        letBndrsThatAreCases' b False expr1 ++
        letBndrsThatAreCases' b False expr2
    letBndrsThatAreCases' b x (Lam _ expr) =
        letBndrsThatAreCases' b x expr --getCaseAltCoreBndrs expr
    letBndrsThatAreCases' b _ (Let bndr expr) =
        letBndrsFromBndr bndr ++ letBndrsThatAreCases' b False expr --getCaseAltCoreBndrs expr
    letBndrsThatAreCases' b True (Case _ _ _ alts) =
        if pred alts
            then b :
                 (alts >>=
                  (\(_, _, expr) -> letBndrsThatAreCases' undefined False expr))
            else (alts >>=
                  (\(_, _, expr) -> letBndrsThatAreCases' undefined False expr))
    letBndrsThatAreCases' b _ (Case _ _ _ alts) =
        (alts >>= (\(_, _, expr) -> letBndrsThatAreCases' b False expr))
    letBndrsThatAreCases' b _ (Cast expr _) = letBndrsThatAreCases' b False expr
    letBndrsThatAreCases' _ _ _ = []
    letBndrsFromBndr :: CoreBind -> [CoreBndr]
    letBndrsFromBndr (NonRec b expr) = letBndrsThatAreCases' b True expr
    letBndrsFromBndr (Rec bs) =
        bs >>= (\(b, expr) -> letBndrsFromBndr $ NonRec b expr)

-- replaces the bndr in let, and call sites with the new bndr.
-- TODO: Replace self-recursive definitions with a loop breaker.
replaceBothBindAndCall :: CoreBndr -> CoreBndr -> CoreExpr -> CoreExpr
replaceBothBindAndCall n n' = everywhere $ mkT go
  where
    go :: CoreExpr -> CoreExpr
    go v@(Var nn)
        | nn == n = Var n'
        | otherwise = v
    go l@(Let (NonRec nn e) expr)
        | nn == n = Let (NonRec n' (replaceBothBindAndCall n n' e)) expr
        | otherwise = Let (NonRec nn (replaceBothBindAndCall n n' e)) expr
    go l@(Let (Rec bees) expr) = Let (Rec $ letrecgo bees) expr
    go x = x
    letrecgo :: [(CoreBndr, CoreExpr)] -> [(CoreBndr, CoreExpr)]
    letrecgo [] = []
    letrecgo ((nn, e):bees)
        | nn == n = (n', replaceBothBindAndCall n n' e) : letrecgo bees
        | otherwise = (nn, replaceBothBindAndCall n n' e) : letrecgo bees

--TODO: Replace self-recursive definitions with a loop breaker.
replaceBind :: CoreBndr -> CoreBndr -> CoreExpr -> CoreExpr
replaceBind n n' = everywhere $ mkT go
  where
    go :: CoreExpr -> CoreExpr
    go l@(Let (NonRec nn e) expr)
        | nn == n = Let (NonRec n' (replaceBind n n' e)) expr
        | otherwise = Let (NonRec nn (replaceBind n n' e)) expr
    go l@(Let (Rec bees) expr) = Let (Rec $ letrecgo bees) expr
    go x = x
    letrecgo :: [(CoreBndr, CoreExpr)] -> [(CoreBndr, CoreExpr)]
    letrecgo [] = []
    letrecgo ((nn, e):bees)
        | nn == n = (n', replaceBind n n' e) : letrecgo bees
        | otherwise = (nn, replaceBind n n' e) : letrecgo bees

-- Sets the inline pragma on a bndr, and forgets the unfolding.
setAlwaysInlineOnBndr :: CoreBndr -> CoreBndr
setAlwaysInlineOnBndr n =
    let Just info = zapUsageInfo $ idInfo n
        unf = unfoldingInfo info
        info' =
            setUnfoldingInfo
                (setInlinePragInfo info alwaysInlinePragma)
                (unfoldCompulsory (arityInfo info) unf)
     in lazySetIdInfo n info'

unfoldCompulsory :: Arity -> Unfolding -> Unfolding
unfoldCompulsory arity cuf@(CoreUnfolding {}) =
    cuf {uf_src=InlineStable, uf_guidance = UnfWhen arity True True}
unfoldCompulsory _ x = NoUnfolding

{-
annotationsOn :: Data a => ModGuts -> DataCon -> CoreM [MAKE_ME_GO_AWAY]
annotationsOn guts dcon = do
    anns <- getAnnotations deserializeWithData guts
    return $ lookupWithDefaultUFM anns [] (getUnique $ dataConTyCon dcon)
-}
{-
    elucidateCore :: DynFlags -> CoreExpr -> CoreM ()
    elucidateCore dflags (App expr1 expr2) = do
      putMsgS "Application args begins: \n"
      putMsgS $ "Application arg1: " ++ take 200 (showSDoc dflags (ppr expr1)) ++ "\n"
      putMsgS $ "Application arg2: " ++ take 200 (showSDoc dflags (ppr expr2)) ++ "\n"
      putMsgS "Elucidating arg1: \n"
      elucidateCore dflags expr1
      putMsgS "Elucidating arg1 ends\n"
      putMsgS "Elucidating expr2: \n"
      elucidateCore dflags expr2
      putMsgS "Elucidating arg2 ends\n"
      putMsgS "Application args ends\n"
    elucidateCore dflags (Lam b expr) = do
      putMsgS $ "Lam Binder: " ++ take 200 (showSDoc dflags (ppr b)) ++ "\n"
      putMsgS $ "Lam Expression: " ++ take 200 (showSDoc dflags (ppr expr)) ++ "\n"
      putMsgS "Elucidating Lam expr: \n"
      elucidateCore dflags expr
      putMsgS "Elucidating Lam ends\n"
    elucidateCore dflags (Let bndr expr) = do
      putMsgS "Let bndr: \n"
      printBind dflags bndr
      putMsgS "Let bndr ends\n"
      putMsgS "Let expr: \n"
      elucidateCore dflags expr
      putMsgS "Let expr ends\n"
    elucidateCore dflags (Cast expr _) = do
      putMsgS "Let the cast begin\n"
      elucidateCore dflags expr
      putMsgS "The cast ends\n"
    elucidateCore _ _ = return ()
-}
