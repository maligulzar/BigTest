//Join 1: x is in both S1 and S2 
//------------------- 
//returns c = 16
(declare-fun S1 (Int) Bool)
(declare-fun S2 (Int) Bool)
(declare-const c Int)
(assert (and (S1 c) (S2 c)))
(assert (and (> c 0) (> c 15)))
(check-sat)
(get-model)


//All 3 cases of join:
//--------------------
//c1 = 16, c2 = 54, c3 = 7735
//S1 = {16, 54} and 7735 is not in S1
//S2 = {16, 7735} and 54 is not in S2

//2nd round
//c1 = 17, c2 = 18, c3 = 40
//S1 = {16, 17, 18, 54}
//S2 = {16, 17, 40, 7735}

//3rd round
//c1 = 19, c2 = 36, c3 = 31
//S1 = {16, 17, 19, 18, 36, 54}
//S2 = {16, 17, 19, 31, 40, 7735}
//--------------------

(declare-fun S1 (Int) Bool)
(declare-fun S2 (Int) Bool)

//E p1: p1.key is in S1 and pA(p1) [== p1.key > 5 and p1.value > 10]
//E p2: p2.key is in S2 and pB(p2) [== p2.key > 15 and p2.value > 20]
//and p1.key = p2.key
//E p1, p2: p1.key is in S1 and p2.key is in S2 and p1.key = p2.key and pA(p1) and pB(p2)

(declare-datatypes (T1 T2) ((Pair (mkPair (first T1) (second T2)))))
(declare-const p1 (Pair Int Int))
(declare-const p2 (Pair Int Int))

(assert (S1 (first p1)) )
(assert (= (first p1) (first p2)))



//E c1: c1 is in S1 and c1 is in S2 and pA(c1) and pB(c1)
(declare-const c1 Int)
(assert (and (S1 c1) (S2 c1)))
(assert (and (> c1 0) (> c1 15)))
(assert (and (not (= c1 7735)) (not (= c1 54)) (not (= c1 16))))
(assert (and (not (= c1 17)) (not (= c1 18)) (not (= c1 40))))

(declare-const c2 Int)
(assert (and (S1 c2) (not (S2 c2))))
(assert (and (> c2 0) (> c2 15)))
(assert (and (not (= c2 7735)) (not (= c2 54)) (not (= c2 16))))
(assert (and (not (= c2 17)) (not (= c2 18)) (not (= c2 40))))

(declare-const c3 Int)
(assert (and (not (S1 c3)) (S2 c3)))
(assert (and (> c3 0) (> c3 15)))
(assert (and (not (= c3 7735)) (not (= c3 54)) (not (= c3 16))))
(assert (and (not (= c3 17)) (not (= c3 18)) (not (= c3 40))))

(check-sat)
(get-model)


//---------------------------- S1 = {1, 2, 16, 17}, S2 = {2, 4, 17, 18}
(declare-fun S1 (Int) Bool)
(declare-fun S2 (Int) Bool)
(assert (forall ((x Int)) 
  (not (xor
    (and (and (and (not (= x 1)) (not (= x 2))) (not (= x 16))) (not (= x 17))) 
    (not (S1 x))))
))
(assert (forall ((x Int)) 
  (not (xor
    (and (and (and (not (= x 2)) (not (= x 4))) (not (= x 17))) (not (= x 18)))
    (not (S2 x))))
))
(check-sat)
(get-model)

(eval (S1 0))
(eval (S1 1))
(eval (S1 2))
(eval (S1 3))
(eval (S1 4))

(eval (S2 0))
(eval (S2 1))
(eval (S2 2))
(eval (S2 3))
(eval (S2 4))
(eval (S2 5))
(eval (S2 6))