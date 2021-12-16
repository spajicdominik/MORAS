(LOOP)
@0
D=M

@LOOPEND
D;JEQ

@100
D = D-1
D = A + D
A = D
D = M

@i
M = D

@0
D = M

@1
M=D-1

@i
D=M

@x
M=D
@0
D=M
@max
M=D

(INNER)
@1
D=M
	
@INNEREND
D;JEQ
	
@100
D = D-1
D = A + D
A = D
D = M

@n
M=D
	
@x
D = M-D
	
@DNS
D;JGT
	
@n
D=M
	
@x
M=D
@1
D=M
@max
M=D
(DNS)
@1
M=M-1

@INNER
0;JMP

(INNEREND)
	
@0
D=M

@100
D=A

@0
D=D+M

@temp
M=D-1

@x
D=M

@temp
A = M
M = D

@100
D=A

@max
D=D+M

@temp
M=D-1

@i
D=M

@temp
A = M
M = D

@0
M = M-1

@LOOP
0;JMP

(LOOPEND)
(END)
@END
0;JMP