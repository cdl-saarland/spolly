; ModuleID = 'ExampleLoopNest.c'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@A = common global [100 x [100 x i32]] zeroinitializer, align 16
@B = common global [100 x [100 x i32]] zeroinitializer, align 16

define void @f() nounwind uwtable {
entry:
  %i = alloca i32, align 4
  %j = alloca i32, align 4
  store i32 1, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc16, %entry
  %0 = load i32* %i, align 4
  %cmp = icmp slt i32 %0, 100
  br i1 %cmp, label %for.body, label %for.end18

for.body:                                         ; preds = %for.cond
  store i32 1, i32* %j, align 4
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc, %for.body
  %1 = load i32* %j, align 4
  %cmp2 = icmp slt i32 %1, 100
  br i1 %cmp2, label %for.body3, label %for.end

for.body3:                                        ; preds = %for.cond1
  %2 = load i32* %j, align 4
  %sub = sub nsw i32 %2, 1
  %idxprom = sext i32 %sub to i64
  %3 = load i32* %i, align 4
  %sub4 = sub nsw i32 %3, 1
  %idxprom5 = sext i32 %sub4 to i64
  %arrayidx = getelementptr inbounds [100 x [100 x i32]]* @A, i32 0, i64 %idxprom5
  %arrayidx6 = getelementptr inbounds [100 x i32]* %arrayidx, i32 0, i64 %idxprom
  %4 = load i32* %arrayidx6, align 4
  %5 = load i32* %j, align 4
  %idxprom7 = sext i32 %5 to i64
  %6 = load i32* %i, align 4
  %sub8 = sub nsw i32 %6, 1
  %idxprom9 = sext i32 %sub8 to i64
  %arrayidx10 = getelementptr inbounds [100 x [100 x i32]]* @B, i32 0, i64 %idxprom9
  %arrayidx11 = getelementptr inbounds [100 x i32]* %arrayidx10, i32 0, i64 %idxprom7
  %7 = load i32* %arrayidx11, align 4
  %mul = mul nsw i32 %4, %7
  %8 = load i32* %j, align 4
  %idxprom12 = sext i32 %8 to i64
  %9 = load i32* %i, align 4
  %idxprom13 = sext i32 %9 to i64
  %arrayidx14 = getelementptr inbounds [100 x [100 x i32]]* @A, i32 0, i64 %idxprom13
  %arrayidx15 = getelementptr inbounds [100 x i32]* %arrayidx14, i32 0, i64 %idxprom12
  store i32 %mul, i32* %arrayidx15, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body3
  %10 = load i32* %j, align 4
  %inc = add nsw i32 %10, 1
  store i32 %inc, i32* %j, align 4
  br label %for.cond1

for.end:                                          ; preds = %for.cond1
  br label %for.inc16

for.inc16:                                        ; preds = %for.end
  %11 = load i32* %i, align 4
  %inc17 = add nsw i32 %11, 1
  store i32 %inc17, i32* %i, align 4
  br label %for.cond

for.end18:                                        ; preds = %for.cond
  ret void
}
