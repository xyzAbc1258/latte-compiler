{-# LANGUAGE QuasiQuotes #-}

module Compiler.Const where

import Text.RawString.QQ

stdLib:: String
stdLib = [r| %struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i64, i32, [20 x i8] }
             %struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }
             
             @.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
             @.str.1 = private unnamed_addr constant [4 x i8] c"%s\0A\00", align 1
             @.str.2 = private unnamed_addr constant [15 x i8] c"runtime error\0A\00", align 1
             @stdin = external global %struct._IO_FILE*, align 8
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define void @printInt(i32) #0 {
               %2 = alloca i32, align 4
               store i32 %0, i32* %2, align 4
               %3 = load i32, i32* %2, align 4
               %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i32 %3)
               ret void
             }
             
             declare i32 @printf(i8*, ...) #1
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define void @printString(i8*) #0 {
               %2 = alloca i8*, align 8
               store i8* %0, i8** %2, align 8
               %3 = load i8*, i8** %2, align 8
               %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i32 0, i32 0), i8* %3)
               ret void
             }
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define void @error() #0 {
               %1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.2, i32 0, i32 0))
               call void @exit(i32 1) #6
               unreachable
                                                               ; No predecessors!
               ret void
             }
             
             ; Function Attrs: noreturn nounwind
             declare void @exit(i32) #2
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define i32 @readInt() #0 {
               %1 = alloca i32, align 4
               %2 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i32* %1)
               %3 = load i32, i32* %1, align 4
               ret i32 %3
             }
             
             declare i32 @__isoc99_scanf(i8*, ...) #1
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define i8* @readString() #0 {
               %1 = alloca i8*, align 8
               %2 = alloca i8*, align 8
               %3 = alloca i64, align 8
               %4 = alloca i64, align 8
               store i64 250, i64* %3, align 8
               %5 = load i64, i64* %3, align 8
               %6 = call noalias i8* @malloc(i64 %5) #7
               store i8* %6, i8** %1, align 8
               %7 = load %struct._IO_FILE*, %struct._IO_FILE** @stdin, align 8
               %8 = call i64 @getline(i8** %1, i64* %3, %struct._IO_FILE* %7)
               store i64 %8, i64* %4, align 8
               %9 = load i64, i64* %4, align 8
               %10 = call noalias i8* @malloc(i64 %9) #7
               store i8* %10, i8** %2, align 8
               %11 = load i8*, i8** %1, align 8
               %12 = load i8*, i8** %2, align 8
               %13 = load i64, i64* %4, align 8
               call void @llvm.memcpy.p0i8.p0i8.i64(i8* %11, i8* %12, i64 %13, i32 1, i1 false)
               %14 = load i8*, i8** %2, align 8
               %15 = load i64, i64* %4, align 8
               %16 = sub i64 %15, 1
               %17 = getelementptr inbounds i8, i8* %14, i64 %16
               store i8 10, i8* %17, align 1
               %18 = load i8*, i8** %1, align 8
               call void @free(i8* %18) #7
               %19 = load i8*, i8** %2, align 8
               ret i8* %19
             }
             
             ; Function Attrs: nounwind
             declare noalias i8* @malloc(i64) #3
             
             declare i64 @getline(i8**, i64*, %struct._IO_FILE*) #1
             
             ; Function Attrs: argmemonly nounwind
             declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i32, i1) #4
             
             ; Function Attrs: nounwind
             declare void @free(i8*) #3
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define i8* @__concatStrings(i8*, i8*) #0 {
               %3 = alloca i8*, align 8
               %4 = alloca i8*, align 8
               %5 = alloca i32, align 4
               %6 = alloca i8*, align 8
               store i8* %0, i8** %3, align 8
               store i8* %1, i8** %4, align 8
               %7 = load i8*, i8** %3, align 8
               %8 = call i64 @strlen(i8* %7) #8
               %9 = load i8*, i8** %4, align 8
               %10 = call i64 @strlen(i8* %9) #8
               %11 = add i64 %8, %10
               %12 = add i64 %11, 1
               %13 = trunc i64 %12 to i32
               store i32 %13, i32* %5, align 4
               %14 = load i32, i32* %5, align 4
               %15 = sext i32 %14 to i64
               %16 = call noalias i8* @malloc(i64 %15) #7
               store i8* %16, i8** %6, align 8
               %17 = load i8*, i8** %6, align 8
               %18 = getelementptr inbounds i8, i8* %17, i64 0
               store i8 10, i8* %18, align 1
               %19 = load i8*, i8** %6, align 8
               %20 = load i8*, i8** %3, align 8
               %21 = call i8* @strcpy(i8* %19, i8* %20) #7
               %22 = load i8*, i8** %6, align 8
               %23 = load i8*, i8** %4, align 8
               %24 = call i8* @strcpy(i8* %22, i8* %23) #7
               %25 = load i8*, i8** %6, align 8
               ret i8* %25
             }

             declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1) #4

             ; Function Attrs: nounwind readonly
             declare i64 @strlen(i8*) #5
             
             ; Function Attrs: nounwind
             declare i8* @strcpy(i8*, i8*) #3
             
             ; Function Attrs: noinline nounwind optnone uwtable
             define i32 @__cmpStrings(i8*, i8*) #0 {
               %3 = alloca i8*, align 8
               %4 = alloca i8*, align 8
               store i8* %0, i8** %3, align 8
               store i8* %1, i8** %4, align 8
               %5 = load i8*, i8** %3, align 8
               %6 = load i8*, i8** %4, align 8
               %7 = call i32 @strcmp(i8* %5, i8* %6) #8
               %8 = icmp eq i32 %7, 0
               %9 = zext i1 %8 to i32
               ret i32 %9
             }
             
             ; Function Attrs: nounwind readonly
             declare i32 @strcmp(i8*, i8*) #5
             
|]
