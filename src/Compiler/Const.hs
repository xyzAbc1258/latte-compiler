{-# LANGUAGE QuasiQuotes #-}

module Compiler.Const where

import Text.RawString.QQ

stdLib:: String
stdLib = [r|
declare noalias i8* @malloc(i64) local_unnamed_addr
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1)
|]