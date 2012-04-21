; ModuleID = 'ExampleLoopNest.s'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@A = common global [100 x [100 x i32]] zeroinitializer, align 16
@B = common global [100 x [100 x i32]] zeroinitializer, align 16

define void @f() nounwind uwtable {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc16, %entry
  %indvar1 = phi i64 [ %indvar.next2, %for.inc16 ], [ 0, %entry ]
  %0 = add i64 %indvar1, 1
  %exitcond3 = icmp ne i64 %indvar1, 99
  br i1 %exitcond3, label %for.body, label %for.end18

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc, %for.body
  %indvar = phi i64 [ %indvar.next, %for.inc ], [ 0, %for.body ]
  %arrayidx6 = getelementptr [100 x [100 x i32]]* @A, i64 0, i64 %indvar1, i64 %indvar
  %1 = add i64 %indvar, 1
  %arrayidx11 = getelementptr [100 x [100 x i32]]* @B, i64 0, i64 %indvar1, i64 %1
  %arrayidx15 = getelementptr [100 x [100 x i32]]* @A, i64 0, i64 %0, i64 %1
  %exitcond = icmp ne i64 %indvar, 99
  br i1 %exitcond, label %for.body3, label %for.end

for.body3:                                        ; preds = %for.cond1
  %2 = load i32* %arrayidx6, align 4
  %3 = load i32* %arrayidx11, align 4
  %mul = mul nsw i32 %2, %3
  store i32 %mul, i32* %arrayidx15, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body3
  %indvar.next = add i64 %indvar, 1
  br label %for.cond1

for.end:                                          ; preds = %for.cond1
  br label %for.inc16

for.inc16:                                        ; preds = %for.end
  %indvar.next2 = add i64 %indvar1, 1
  br label %for.cond

for.end18:                                        ; preds = %for.cond
  ret void
}
