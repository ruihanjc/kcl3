
.class public or.or
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method


.method public static writes(Ljava/lang/String;)V
    .limit stack 2
    .limit locals 1
    getstatic java/lang/System/out Ljava/io/PrintStream;
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return
.end method


.method public static read()I 
    .limit locals 10 
    .limit stack 10

    ldc 0 
    istore 1  ; this will hold our final integer 
Label1: 
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I 
    istore 2 
    iload 2 
    ldc 13   ; the newline delimiter 
    isub 
    ifeq Label2 
    iload 2 
    ldc 32   ; the space delimiter 
    isub 
    ifeq Label2

    iload 2 
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48 
    isub 
    ldc 10 
    iload 1 
    imul 
    iadd 
    istore 1 
    goto Label1 
Label2: 
    ; when we come here we have our integer computed in local variable 1 
    iload 1 
    ireturn 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

   ldc 2
   istore 0 		; f
   ldc 1
   istore 1 		; i
Loop_begin_0:
   iload 0 		; f
   ldc 4
   if_icmpge Or_else_2
   goto Or_end_3
Or_else_2:
   iload 0 		; f
   ldc 3
   if_icmpge Loop_end_1
Or_end_3:
   iload 1 		; i
   invokestatic or/or/write(I)V
   iload 1 		; i
   ldc 1
   iadd
   istore 1 		; i
   iload 0 		; f
   ldc 1
   iadd
   istore 0 		; f
   goto Loop_begin_0
Loop_end_1:

; COMPILED CODE ENDS
   return

.end method