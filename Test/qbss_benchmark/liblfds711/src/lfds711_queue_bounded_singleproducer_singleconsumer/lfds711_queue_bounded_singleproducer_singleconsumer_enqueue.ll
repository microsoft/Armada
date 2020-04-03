; ModuleID = 'lfds711_queue_bounded_singleproducer_singleconsumer_enqueue.c'
source_filename = "lfds711_queue_bounded_singleproducer_singleconsumer_enqueue.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.lfds711_queue_bss_state = type { i64, i64, i64, i64, %struct.lfds711_queue_bss_element*, i8* }
%struct.lfds711_queue_bss_element = type { i8*, i8* }

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @lfds711_queue_bss_enqueue(%struct.lfds711_queue_bss_state*, i8*, i8*) #0 {
  %4 = alloca i32, align 4
  %5 = alloca %struct.lfds711_queue_bss_state*, align 8
  %6 = alloca i8*, align 8
  %7 = alloca i8*, align 8
  %8 = alloca %struct.lfds711_queue_bss_element*, align 8
  %9 = alloca i8*, align 8
  store %struct.lfds711_queue_bss_state* %0, %struct.lfds711_queue_bss_state** %5, align 8
  store i8* %1, i8** %6, align 8
  store i8* %2, i8** %7, align 8
  %10 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %11 = icmp ne %struct.lfds711_queue_bss_state* %10, null
  br i1 %11, label %14, label %12

12:                                               ; preds = %3
  store i8* null, i8** %9, align 8
  %13 = load i8*, i8** %9, align 8
  store i8 0, i8* %13, align 1
  br label %14

14:                                               ; preds = %12, %3
  call void @lfds711_pal_barrier_compiler()
  fence seq_cst
  call void @lfds711_pal_barrier_compiler()
  %15 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %16 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %15, i32 0, i32 3
  %17 = load volatile i64, i64* %16, align 8
  %18 = add i64 %17, 1
  %19 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %20 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %19, i32 0, i32 1
  %21 = load i64, i64* %20, align 8
  %22 = and i64 %18, %21
  %23 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %24 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %23, i32 0, i32 2
  %25 = load volatile i64, i64* %24, align 8
  %26 = icmp ne i64 %22, %25
  br i1 %26, label %27, label %51

27:                                               ; preds = %14
  %28 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %29 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %28, i32 0, i32 4
  %30 = load %struct.lfds711_queue_bss_element*, %struct.lfds711_queue_bss_element** %29, align 8
  %31 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %32 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %31, i32 0, i32 3
  %33 = load volatile i64, i64* %32, align 8
  %34 = getelementptr inbounds %struct.lfds711_queue_bss_element, %struct.lfds711_queue_bss_element* %30, i64 %33
  store %struct.lfds711_queue_bss_element* %34, %struct.lfds711_queue_bss_element** %8, align 8
  %35 = load i8*, i8** %6, align 8
  %36 = load %struct.lfds711_queue_bss_element*, %struct.lfds711_queue_bss_element** %8, align 8
  %37 = getelementptr inbounds %struct.lfds711_queue_bss_element, %struct.lfds711_queue_bss_element* %36, i32 0, i32 0
  store volatile i8* %35, i8** %37, align 8
  %38 = load i8*, i8** %7, align 8
  %39 = load %struct.lfds711_queue_bss_element*, %struct.lfds711_queue_bss_element** %8, align 8
  %40 = getelementptr inbounds %struct.lfds711_queue_bss_element, %struct.lfds711_queue_bss_element* %39, i32 0, i32 1
  store volatile i8* %38, i8** %40, align 8
  call void @lfds711_pal_barrier_compiler()
  fence seq_cst
  call void @lfds711_pal_barrier_compiler()
  %41 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %42 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %41, i32 0, i32 3
  %43 = load volatile i64, i64* %42, align 8
  %44 = add i64 %43, 1
  %45 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %46 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %45, i32 0, i32 1
  %47 = load i64, i64* %46, align 8
  %48 = and i64 %44, %47
  %49 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %5, align 8
  %50 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %49, i32 0, i32 3
  store volatile i64 %48, i64* %50, align 8
  store i32 1, i32* %4, align 4
  br label %52

51:                                               ; preds = %14
  store i32 0, i32* %4, align 4
  br label %52

52:                                               ; preds = %51, %27
  %53 = load i32, i32* %4, align 4
  ret i32 %53
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define internal void @lfds711_pal_barrier_compiler() #0 {
  call void asm sideeffect "", "~{memory},~{dirflag},~{fpsr},~{flags}"() #1, !srcloc !4
  ret void
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{!"clang version 9.0.1 "}
!4 = !{i32 51241}
