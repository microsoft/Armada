; ModuleID = 'lfds711_queue_bounded_singleproducer_singleconsumer_enqueue.c'
source_filename = "lfds711_queue_bounded_singleproducer_singleconsumer_enqueue.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.lfds711_queue_bss_state = type { i64, i64, i64, i64, %struct.lfds711_queue_bss_element*, i8* }
%struct.lfds711_queue_bss_element = type { i8*, i8* }

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @lfds711_queue_bss_enqueue(%struct.lfds711_queue_bss_state* %qbsss, i8* %key, i8* %value) #0 {
entry:
  %retval = alloca i32, align 4
  %qbsss.addr = alloca %struct.lfds711_queue_bss_state*, align 8
  %key.addr = alloca i8*, align 8
  %value.addr = alloca i8*, align 8
  %qbsse = alloca %struct.lfds711_queue_bss_element*, align 8
  %c = alloca i8*, align 8
  store %struct.lfds711_queue_bss_state* %qbsss, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  store i8* %key, i8** %key.addr, align 8
  store i8* %value, i8** %value.addr, align 8
  %0 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %cmp = icmp ne %struct.lfds711_queue_bss_state* %0, null
  br i1 %cmp, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  store i8* null, i8** %c, align 8
  %1 = load i8*, i8** %c, align 8
  store i8 0, i8* %1, align 1
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  call void @lfds711_pal_barrier_compiler()
  fence seq_cst
  call void @lfds711_pal_barrier_compiler()
  %2 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %write_index = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %2, i32 0, i32 3
  %3 = load volatile i64, i64* %write_index, align 8
  %add = add i64 %3, 1
  %4 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %mask = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %4, i32 0, i32 1
  %5 = load i64, i64* %mask, align 8
  %and = and i64 %add, %5
  %6 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %read_index = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %6, i32 0, i32 2
  %7 = load volatile i64, i64* %read_index, align 8
  %cmp1 = icmp ne i64 %and, %7
  br i1 %cmp1, label %if.then2, label %if.end11

if.then2:                                         ; preds = %if.end
  %8 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %element_array = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %8, i32 0, i32 4
  %9 = load %struct.lfds711_queue_bss_element*, %struct.lfds711_queue_bss_element** %element_array, align 8
  %10 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %write_index3 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %10, i32 0, i32 3
  %11 = load volatile i64, i64* %write_index3, align 8
  %add.ptr = getelementptr inbounds %struct.lfds711_queue_bss_element, %struct.lfds711_queue_bss_element* %9, i64 %11
  store %struct.lfds711_queue_bss_element* %add.ptr, %struct.lfds711_queue_bss_element** %qbsse, align 8
  %12 = load i8*, i8** %key.addr, align 8
  %13 = load %struct.lfds711_queue_bss_element*, %struct.lfds711_queue_bss_element** %qbsse, align 8
  %key4 = getelementptr inbounds %struct.lfds711_queue_bss_element, %struct.lfds711_queue_bss_element* %13, i32 0, i32 0
  store volatile i8* %12, i8** %key4, align 8
  %14 = load i8*, i8** %value.addr, align 8
  %15 = load %struct.lfds711_queue_bss_element*, %struct.lfds711_queue_bss_element** %qbsse, align 8
  %value5 = getelementptr inbounds %struct.lfds711_queue_bss_element, %struct.lfds711_queue_bss_element* %15, i32 0, i32 1
  store volatile i8* %14, i8** %value5, align 8
  call void @lfds711_pal_barrier_compiler()
  fence seq_cst
  call void @lfds711_pal_barrier_compiler()
  %16 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %write_index6 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %16, i32 0, i32 3
  %17 = load volatile i64, i64* %write_index6, align 8
  %add7 = add i64 %17, 1
  %18 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %mask8 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %18, i32 0, i32 1
  %19 = load i64, i64* %mask8, align 8
  %and9 = and i64 %add7, %19
  %20 = load %struct.lfds711_queue_bss_state*, %struct.lfds711_queue_bss_state** %qbsss.addr, align 8
  %write_index10 = getelementptr inbounds %struct.lfds711_queue_bss_state, %struct.lfds711_queue_bss_state* %20, i32 0, i32 3
  store volatile i64 %and9, i64* %write_index10, align 8
  store i32 1, i32* %retval, align 4
  br label %return

if.end11:                                         ; preds = %if.end
  store i32 0, i32* %retval, align 4
  br label %return

return:                                           ; preds = %if.end11, %if.then2
  %21 = load i32, i32* %retval, align 4
  ret i32 %21
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define internal void @lfds711_pal_barrier_compiler() #0 {
entry:
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
