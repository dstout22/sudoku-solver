;declares an array of arrays holding integers (the rows of the puzzle)
(declare-fun a (Int Int) Int)

;asserts that every row contains each instance of the numbers 1-9 once
(assert  
     (forall ((i Int) (n Int)) 
           (=> (and(< i 9)(< -1 i)(< n 10)(< 0 n))
               (exists ((j Int)) 
                    (and(< j 9)(< -1 j)(=(a i j) n)))
)))

;asserts that every column contains each instance of the numbers 1-9 once
(assert  
     (forall ((i Int) (n Int)) 
          (=>(and(< i 9)(< -1 i)(< n 10)(< 0 n))
               (exists ((j Int)) 
                    (and(< j 9)(< -1 j)(=(a j i) n)))
     )
))

;asserts that in every box (for example 0,0 through 2,2)
;contains exactly one instance of the number 1 through 9
(assert(forall ((n Int) (x Int) (y Int)) 
     (=> (and(< 0 n)(< n 10)(or (= x 0)(= x 3)(= x 6))(or (= y 0)(= y 3)(= y 6)))
          (exists ((i Int) (j Int)) (and(<= x i)(< i (+ x 3))(<= y j)(< j (+ y 3))(= (a i j) n)(distinct (a x y) (a x (+ y 1)) (a x (+ y 2))
                (a (+ x 1) y) (a (+ x 1) (+ y 1)) (a (+ x 1) (+ y 2))
                (a (+ x 2) y) (a (+ x 2) (+ y 1)) (a (+ x 2) (+ y 2))))))
))

; *Dynamic Portion*

; Example initial Sudoku numbers - from ChatGPT
; Row 0
(assert (= (a 0 0) 5))
(assert (= (a 0 1) 3))
(assert (= (a 0 4) 7))

; Row 1
(assert (= (a 1 0) 6))
(assert (= (a 1 3) 1))
(assert (= (a 1 4) 9))
(assert (= (a 1 5) 5))

; Row 2
(assert (= (a 2 1) 9))
(assert (= (a 2 2) 8))
(assert (= (a 2 7) 6))

; Row 3
(assert (= (a 3 0) 8))
(assert (= (a 3 4) 6))
(assert (= (a 3 8) 3))

; Row 4
(assert (= (a 4 0) 4))
(assert (= (a 4 3) 8))
(assert (= (a 4 5) 3))
(assert (= (a 4 8) 1))

; Row 5
(assert (= (a 5 0) 7))
(assert (= (a 5 4) 2))
(assert (= (a 5 8) 6))

; Row 6
(assert (= (a 6 1) 6))
(assert (= (a 6 6) 2))
(assert (= (a 6 7) 8))

; Row 7
(assert (= (a 7 3) 4))
(assert (= (a 7 4) 1))
(assert (= (a 7 5) 9))
(assert (= (a 7 8) 5))

; Row 8
(assert (= (a 8 4) 8))
(assert (= (a 8 7) 7))
(assert (= (a 8 8) 9))

;checks satisfiability
(check-sat)
(get-value (
  (a 0 0) (a 0 1) (a 0 2) (a 0 3) (a 0 4) (a 0 5) (a 0 6) (a 0 7) (a 0 8)
  (a 1 0) (a 1 1) (a 1 2) (a 1 3) (a 1 4) (a 1 5) (a 1 6) (a 1 7) (a 1 8)
  (a 2 0) (a 2 1) (a 2 2) (a 2 3) (a 2 4) (a 2 5) (a 2 6) (a 2 7) (a 2 8)
  (a 3 0) (a 3 1) (a 3 2) (a 3 3) (a 3 4) (a 3 5) (a 3 6) (a 3 7) (a 3 8)
  (a 4 0) (a 4 1) (a 4 2) (a 4 3) (a 4 4) (a 4 5) (a 4 6) (a 4 7) (a 4 8)
  (a 5 0) (a 5 1) (a 5 2) (a 5 3) (a 5 4) (a 5 5) (a 5 6) (a 5 7) (a 5 8)
  (a 6 0) (a 6 1) (a 6 2) (a 6 3) (a 6 4) (a 6 5) (a 6 6) (a 6 7) (a 6 8)
  (a 7 0) (a 7 1) (a 7 2) (a 7 3) (a 7 4) (a 7 5) (a 7 6) (a 7 7) (a 7 8)
  (a 8 0) (a 8 1) (a 8 2) (a 8 3) (a 8 4) (a 8 5) (a 8 6) (a 8 7) (a 8 8)
))