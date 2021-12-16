@1
D = M
@e
M = D
@SKIP
D;JGT
@2
M=1

@END
0;JMP

(SKIP)
@0
D = M
@i
M = D

@SKIP1
D-1;JGT
@2
M=1

@END
0;JMP

(SKIP1)
@2
M = D
@j
M = D

(OUTER_START)
@e
D = M

@OUTER_END
D-1;JEQ

(LOOP_START)
@i
D = M

@LOOP_END
D-1;JEQ
@j
D = M
@2
M = M + D
@i
M = M - 1

@LOOP_START
0;JMP

(LOOP_END)
@2
D = M
@j
M = D
@0
D = M
@i
M = D
@e
M = M-1

@OUTER_START
0;JMP

(OUTER_END)
(END)
@END
0;JMP