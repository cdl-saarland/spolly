; ModuleID = 'ExampleLoopNest.ll'
target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@A = common global [100 x [100 x i32]] zeroinitializer, align 16
@B = common global [100 x [100 x i32]] zeroinitializer, align 16

define void @f() nounwind uwtable {
entry:
  br label %polly.split_new_and_old

polly.split_new_and_old:                          ; preds = %entry
  br i1 true, label %polly.start, label %for.cond

for.cond:                                         ; preds = %polly.split_new_and_old, %for.inc16
  %indvar1 = phi i64 [ %indvar.next2, %for.inc16 ], [ 0, %polly.split_new_and_old ]
  %exitcond3 = icmp ne i64 %indvar1, 99
  br i1 %exitcond3, label %for.body, label %polly.merge_new_and_old

for.body:                                         ; preds = %for.cond
  br label %for.cond1

for.cond1:                                        ; preds = %for.inc, %for.body
  %indvar = phi i64 [ %indvar.next, %for.inc ], [ 0, %for.body ]
  %exitcond = icmp ne i64 %indvar, 99
  br i1 %exitcond, label %for.body3, label %for.end

for.body3:                                        ; preds = %for.cond1
  %arrayidx6.moved.to.for.body3 = getelementptr [100 x [100 x i32]]* @A, i64 0, i64 %indvar1, i64 %indvar
  %.moved.to.for.body3 = add i64 %indvar, 1
  %arrayidx11.moved.to.for.body3 = getelementptr [100 x [100 x i32]]* @B, i64 0, i64 %indvar1, i64 %.moved.to.for.body3
  %.moved.to.for.body31 = add i64 %indvar1, 1
  %arrayidx15.moved.to.for.body3 = getelementptr [100 x [100 x i32]]* @A, i64 0, i64 %.moved.to.for.body31, i64 %.moved.to.for.body3
  %0 = load i32* %arrayidx6.moved.to.for.body3, align 4
  %1 = load i32* %arrayidx11.moved.to.for.body3, align 4
  %mul = mul nsw i32 %0, %1
  store i32 %mul, i32* %arrayidx15.moved.to.for.body3, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body3
  %indvar.next = add i64 %indvar, 1
  br label %for.cond1

for.end:                                          ; preds = %for.cond1
  br label %for.inc16

for.inc16:                                        ; preds = %for.end
  %indvar.next2 = add i64 %indvar1, 1
  br label %for.cond

polly.merge_new_and_old:                          ; preds = %polly.loop_after, %for.cond
  ret void

polly.start:                                      ; preds = %polly.split_new_and_old
  br label %polly.loop_header

polly.loop_after:                                 ; preds = %polly.loop_header
  br label %polly.merge_new_and_old

polly.loop_header:                                ; preds = %polly.loop_after4, %polly.start
  %polly.loopiv = phi i64 [ -128, %polly.start ], [ %polly.next_loopiv, %polly.loop_after4 ]
  %polly.next_loopiv = add i64 %polly.loopiv, 32
  %2 = icmp sle i64 %polly.loopiv, 98
  br i1 %2, label %polly.loop_body, label %polly.loop_after

polly.loop_body:                                  ; preds = %polly.loop_header
  %3 = mul i64 1, %polly.loopiv
  %4 = sub i64 %3, 32
  %5 = add i64 %4, 1
  %6 = icmp slt i64 %3, 0
  %7 = select i1 %6, i64 %5, i64 %3
  %8 = sdiv i64 %7, 32
  %9 = mul i64 -32, %8
  %10 = add i64 %9, -32
  %11 = icmp sgt i64 0, %10
  %12 = select i1 %11, i64 0, i64 %10
  %13 = mul i64 -1, %polly.loopiv
  %14 = add i64 %13, 98
  %15 = icmp slt i64 98, %14
  %16 = select i1 %15, i64 98, i64 %14
  br label %polly.loop_header2

polly.loop_after4:                                ; preds = %polly.loop_header2
  br label %polly.loop_header

polly.loop_header2:                               ; preds = %polly.loop_after9, %polly.loop_body
  %polly.loopiv5 = phi i64 [ %12, %polly.loop_body ], [ %polly.next_loopiv6, %polly.loop_after9 ]
  %polly.next_loopiv6 = add i64 %polly.loopiv5, 32
  %17 = icmp sle i64 %polly.loopiv5, %16
  br i1 %17, label %polly.loop_body3, label %polly.loop_after4

polly.loop_body3:                                 ; preds = %polly.loop_header2
  %18 = mul i64 1, %polly.loopiv
  %19 = icmp sgt i64 -98, %18
  %20 = select i1 %19, i64 -98, i64 %18
  %21 = mul i64 -1, %polly.loopiv5
  %22 = add i64 %21, -31
  %23 = icmp sgt i64 %20, %22
  %24 = select i1 %23, i64 %20, i64 %22
  %25 = mul i64 1, %polly.loopiv
  %26 = add i64 %25, 31
  %27 = mul i64 -1, %polly.loopiv5
  %28 = add i64 %27, 98
  %29 = icmp slt i64 %26, %28
  %30 = select i1 %29, i64 %26, i64 %28
  br label %polly.loop_header7

polly.loop_after9:                                ; preds = %polly.loop_header7
  br label %polly.loop_header2

polly.loop_header7:                               ; preds = %polly.loop_after14, %polly.loop_body3
  %polly.loopiv10 = phi i64 [ %24, %polly.loop_body3 ], [ %polly.next_loopiv11, %polly.loop_after14 ]
  %polly.next_loopiv11 = add i64 %polly.loopiv10, 1
  %31 = icmp sle i64 %polly.loopiv10, %30
  br i1 %31, label %polly.loop_body8, label %polly.loop_after9

polly.loop_body8:                                 ; preds = %polly.loop_header7
  %32 = mul i64 1, %polly.loopiv5
  %33 = mul i64 -1, %polly.loopiv10
  %34 = icmp sgt i64 %32, %33
  %35 = select i1 %34, i64 %32, i64 %33
  %36 = mul i64 1, %polly.loopiv5
  %37 = add i64 %36, 31
  %38 = icmp slt i64 98, %37
  %39 = select i1 %38, i64 98, i64 %37
  %40 = mul i64 -1, %polly.loopiv10
  %41 = add i64 %40, 98
  %42 = icmp slt i64 %39, %41
  %43 = select i1 %42, i64 %39, i64 %41
  br label %polly.loop_header12

polly.loop_after14:                               ; preds = %polly.loop_header12
  br label %polly.loop_header7

polly.loop_header12:                              ; preds = %polly.stmt.for.body3, %polly.loop_body8
  %polly.loopiv15 = phi i64 [ %35, %polly.loop_body8 ], [ %polly.next_loopiv16, %polly.stmt.for.body3 ]
  %polly.next_loopiv16 = add i64 %polly.loopiv15, 1
  %44 = icmp sle i64 %polly.loopiv15, %43
  br i1 %44, label %polly.loop_body13, label %polly.loop_after14

polly.loop_body13:                                ; preds = %polly.loop_header12
  %45 = mul i64 1, %polly.loopiv10
  %46 = mul i64 1, %polly.loopiv15
  %47 = add i64 %45, %46
  %48 = mul i64 1, %polly.loopiv15
  br label %polly.stmt.for.body3

polly.stmt.for.body3:                             ; preds = %polly.loop_body13
  %p_arrayidx6.moved.to.for.body3 = getelementptr [100 x [100 x i32]]* @A, i64 0, i64 %47, i64 %48
  %p_.moved.to.for.body3 = add i64 %48, 1
  %p_arrayidx11.moved.to.for.body3 = getelementptr [100 x [100 x i32]]* @B, i64 0, i64 %47, i64 %p_.moved.to.for.body3
  %p_.moved.to.for.body31 = add i64 %47, 1
  %p_arrayidx15.moved.to.for.body3 = getelementptr [100 x [100 x i32]]* @A, i64 0, i64 %p_.moved.to.for.body31, i64 %p_.moved.to.for.body3
  %_p_scalar_ = load i32* %p_arrayidx6.moved.to.for.body3
  %_p_scalar_17 = load i32* %p_arrayidx11.moved.to.for.body3
  %p_mul = mul nsw i32 %_p_scalar_, %_p_scalar_17
  store i32 %p_mul, i32* %p_arrayidx15.moved.to.for.body3
  br label %polly.loop_header12
}
