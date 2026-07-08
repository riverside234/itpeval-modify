(* ========================================================================= *)
(* Determinant and trace of a square matrix.                                 *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Multivariate/vectors.ml";;
needs "Library/permutations.ml";;
needs "Library/floor.ml";;
needs "Library/products.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Trace of a matrix (this is relatively easy).                              *)
(* ------------------------------------------------------------------------- *)

let trace = new_definition
  `(trace:real^N^N->real) A = sum(1..dimindex(:N)) (\i. A$i$i)`;;

let TRACE_0 = `trace(mat 0) = &0`;;

let TRACE_I = `trace(mat 1 :real^N^N) = &(dimindex(:N))`;;

let TRACE_ADD = `!A B:real^N^N. trace(A + B) = trace(A) + trace(B)`;;

let TRACE_SUB = `!A B:real^N^N. trace(A - B) = trace(A) - trace(B)`;;

let TRACE_CMUL = `!c A:real^N^N. trace(c %% A) = c * trace A`;;

let TRACE_NEG = `!A:real^N^N. trace(--A) = --(trace A)`;;

let TRACE_MUL_SYM = `!A B:real^N^M. trace(A ** B) = trace(B ** A)`;;

let TRACE_TRANSP = `!A:real^N^N. trace(transp A) = trace A`;;

let TRACE_SIMILAR = `!A:real^N^N U:real^N^N.
        invertible U ==> trace(matrix_inv U ** A ** U) = trace A`;;

let TRACE_MUL_CYCLIC = `!A:real^P^M B C:real^M^N. trace(A ** B ** C) = trace(B ** C ** A)`;;

(* ------------------------------------------------------------------------- *)
(* Definition of determinant.                                                *)
(* ------------------------------------------------------------------------- *)

let det = new_definition
 `det(A:real^N^N) =
        sum { p | p permutes 1..dimindex(:N) }
            (\p. sign(p) * product (1..dimindex(:N)) (\i. A$i$(p i)))`;;

(* ------------------------------------------------------------------------- *)
(* A few general lemmas we need below.                                       *)
(* ------------------------------------------------------------------------- *)

let IN_DIMINDEX_SWAP = `!m n j. 1 <= m /\ m <= dimindex(:N) /\
             1 <= n /\ n <= dimindex(:N) /\
             1 <= j /\ j <= dimindex(:N)
           ==> 1 <= swap(m,n) j /\ swap(m,n) j <= dimindex(:N)`;;

let LAMBDA_BETA_PERM = `!p i. p permutes 1..dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N)
         ==> ((lambda) g :A^N) $ p(i) = g(p i)`;;

let PRODUCT_PERMUTE = `!f p s. p permutes s ==> product s f = product s (f o p)`;;

let PRODUCT_PERMUTE_NUMSEG = `!f p m n. p permutes m..n ==> product(m..n) f = product(m..n) (f o p)`;;

let REAL_MUL_SUM = `!s t f g.
        FINITE s /\ FINITE t
        ==> sum s f * sum t g = sum s (\i. sum t (\j. f(i) * g(j)))`;;

let REAL_MUL_SUM_NUMSEG = `!m n p q. sum(m..n) f * sum(p..q) g =
             sum(m..n) (\i. sum(p..q) (\j. f(i) * g(j)))`;;

(* ------------------------------------------------------------------------- *)
(* Basic determinant properties.                                             *)
(* ------------------------------------------------------------------------- *)

let DET_CMUL = `!A:real^N^N c. det(c %% A) = c pow dimindex(:N) * det A`;;

let DET_NEG = `!A:real^N^N. det(--A) = --(&1) pow dimindex(:N) * det A`;;

let DET_TRANSP = `!A:real^N^N. det(transp A) = det A`;;

let DET_LOWERTRIANGULAR = `!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ i < j ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`;;

let DET_UPPERTRIANGULAR = `!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ j < i ==> A$i$j = &0)
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`;;

let DET_I = `det(mat 1 :real^N^N) = &1`;;

let DET_0 = `det(mat 0 :real^N^N) = &0`;;

let DET_PERMUTE_ROWS = `!A:real^N^N p.
        p permutes 1..dimindex(:N)
        ==> det(lambda i. A$p(i)) = sign(p) * det(A)`;;

let DET_PERMUTE_COLUMNS = `!A:real^N^N p.
        p permutes 1..dimindex(:N)
        ==> det((lambda i j. A$i$p(j)):real^N^N) = sign(p) * det(A)`;;

let DET_IDENTICAL_ROWS = `!A:real^N^N i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
                    row i A = row j A
                    ==> det A = &0`;;

let DET_IDENTICAL_COLUMNS = `!A:real^N^N i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j) /\
                    column i A = column j A
                    ==> det A = &0`;;

let DET_ZERO_ROW = `!A:real^N^N i.
       1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0  ==> det A = &0`;;

let DET_ZERO_COLUMN = `!A:real^N^N i.
       1 <= i /\ i <= dimindex(:N) /\ column i A = vec 0  ==> det A = &0`;;

let DET_ROW_ADD = `!a b c k.
         1 <= k /\ k <= dimindex(:N)
         ==> det((lambda i. if i = k then a + b else c i):real^N^N) =
             det((lambda i. if i = k then a else c i):real^N^N) +
             det((lambda i. if i = k then b else c i):real^N^N)`;;

let DET_ROW_MUL = `!a b c k.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i. if i = k then c % a else b i):real^N^N) =
            c * det((lambda i. if i = k then a else b i):real^N^N)`;;

let DET_ROW_OPERATION = `!A:real^N^N i.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
        ==> det(lambda k. if k = i then row i A + c % row j A else row k A) =
            det A`;;

let DET_ROW_SPAN = `!A:real^N^N i x.
        1 <= i /\ i <= dimindex(:N) /\
        x IN span {row j A | 1 <= j /\ j <= dimindex(:N) /\ ~(j = i)}
        ==> det(lambda k. if k = i then row i A + x else row k A) =
            det A`;;

(* ------------------------------------------------------------------------- *)
(* May as well do this, though it's a bit unsatisfactory since it ignores    *)
(* exact duplicates by considering the rows/columns as a set.                *)
(* ------------------------------------------------------------------------- *)

let DET_DEPENDENT_ROWS = `!A:real^N^N. dependent(rows A) ==> det A = &0`;;

let DET_DEPENDENT_COLUMNS = `!A:real^N^N. dependent(columns A) ==> det A = &0`;;

(* ------------------------------------------------------------------------- *)
(* Multilinearity and the multiplication formula.                            *)
(* ------------------------------------------------------------------------- *)

let DET_LINEAR_ROW_VSUM = `!a c s k.
         FINITE s /\ 1 <= k /\ k <= dimindex(:N)
         ==> det((lambda i. if i = k then vsum s a else c i):real^N^N) =
             sum s
               (\j. det((lambda i. if i = k then a(j) else c i):real^N^N))`;;

let BOUNDED_FUNCTIONS_BIJECTIONS_1 = `!p. p IN {(y,g) | y IN s /\
                     g IN {f | (!i. 1 <= i /\ i <= k ==> f i IN s) /\
                               (!i. ~(1 <= i /\ i <= k) ==> f i = i)}}
       ==> (\(y,g) i. if i = SUC k then y else g(i)) p IN
             {f | (!i. 1 <= i /\ i <= SUC k ==> f i IN s) /\
                  (!i. ~(1 <= i /\ i <= SUC k) ==> f i = i)} /\
           (\h. h(SUC k),(\i. if i = SUC k then i else h(i)))
            ((\(y,g) i. if i = SUC k then y else g(i)) p) = p`;;

let BOUNDED_FUNCTIONS_BIJECTIONS_2 = `!h. h IN {f | (!i. 1 <= i /\ i <= SUC k ==> f i IN s) /\
                 (!i. ~(1 <= i /\ i <= SUC k) ==> f i = i)}
       ==> (\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h IN
           {(y,g) | y IN s /\
                     g IN {f | (!i. 1 <= i /\ i <= k ==> f i IN s) /\
                               (!i. ~(1 <= i /\ i <= k) ==> f i = i)}} /\
           (\(y,g) i. if i = SUC k then y else g(i))
              ((\h. h(SUC k),(\i. if i = SUC k then i else h(i))) h) = h`;;

let FINITE_BOUNDED_FUNCTIONS = `!s k. FINITE s
         ==> FINITE {f | (!i. 1 <= i /\ i <= k ==> f(i) IN s) /\
                         (!i. ~(1 <= i /\ i <= k) ==> f(i) = i)}`;;

let DET_LINEAR_ROWS_VSUM_LEMMA = `!s k a c.
         FINITE s /\ k <= dimindex(:N)
         ==> det((lambda i. if i <= k then vsum s (a i) else c i):real^N^N) =
             sum {f | (!i. 1 <= i /\ i <= k ==> f(i) IN s) /\
                      !i. ~(1 <= i /\ i <= k) ==> f(i) = i}
                 (\f. det((lambda i. if i <= k then a i (f i) else c i)
                          :real^N^N))`;;

let DET_LINEAR_ROWS_VSUM = `!s a.
         FINITE s
         ==> det((lambda i. vsum s (a i)):real^N^N) =
             sum {f | (!i. 1 <= i /\ i <= dimindex(:N) ==> f(i) IN s) /\
                      !i. ~(1 <= i /\ i <= dimindex(:N)) ==> f(i) = i}
                 (\f. det((lambda i. a i (f i)):real^N^N))`;;

let MATRIX_MUL_VSUM_ALT = `!A:real^N^N B:real^N^N. A ** B =
                  lambda i. vsum (1..dimindex(:N)) (\k. A$i$k % B$k)`;;

let DET_ROWS_MUL = `!a c. det((lambda i. c(i) % a(i)):real^N^N) =
         product(1..dimindex(:N)) (\i. c(i)) *
         det((lambda i. a(i)):real^N^N)`;;

let DET_MUL = `!A B:real^N^N. det(A ** B) = det(A) * det(B)`;;

let DET_LINEAR_ROWS = `!f:real^N->real^N A:real^N^N.
        linear f ==> det(lambda i. f(A$i)) = det(matrix f) * det A`;;

(* ------------------------------------------------------------------------- *)
(* Relation to invertibility.                                                *)
(* ------------------------------------------------------------------------- *)

let INVERTIBLE_DET_NZ = `!A:real^N^N. invertible(A) <=> ~(det A = &0)`;;

let DET_EQ_0 = `!A:real^N^N. det(A) = &0 <=> ~invertible(A)`;;

let DET_MATRIX_INV = `!A:real^N^N. det(matrix_inv A) = inv(det A)`;;

let MATRIX_MUL_LINV = `!A:real^N^N. ~(det A = &0) ==> matrix_inv A ** A = mat 1`;;

let MATRIX_MUL_RINV = `!A:real^N^N. ~(det A = &0) ==> A ** matrix_inv A = mat 1`;;

let DET_MATRIX_EQ_0 = `!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ f o g = I /\ g o f = I))`;;

let DET_MATRIX_EQ_0_LEFT = `!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ g o f = I))`;;

let DET_MATRIX_EQ_0_RIGHT = `!f:real^N->real^N.
        linear f
        ==> (det(matrix f) = &0 <=>
             ~(?g. linear g /\ f o g = I))`;;

let DET_EQ_0_RANK = `!A:real^N^N. det A = &0 <=> rank A < dimindex(:N)`;;

let RANK_EQ_FULL_DET = `!A:real^N^N. rank A = dimindex(:N) <=> ~(det A = &0)`;;

let INVERTIBLE_COVARIANCE_RANK = `!A:real^N^M. invertible(transp A ** A) <=> rank A = dimindex(:N)`;;

let HOMOGENEOUS_LINEAR_EQUATIONS_DET = `!A:real^N^N. (?x. ~(x = vec 0) /\ A ** x = vec 0) <=> det A = &0`;;

let INVERTIBLE_MATRIX_MUL = `!A:real^N^N B:real^N^N.
        invertible(A ** B) <=> invertible A /\ invertible B`;;

let MATRIX_INV_MUL = `!A:real^N^N B:real^N^N.
        invertible A /\ invertible B
        ==> matrix_inv(A ** B) = matrix_inv B ** matrix_inv A`;;

let DET_SIMILAR = `!S:real^N^N A. invertible S ==> det(matrix_inv S ** A ** S) = det A`;;

let INVERTIBLE_NEARBY_ONORM = `!A B:real^N^N.
        invertible A /\
        onorm(\x. (B - A) ** x) < inv(onorm(\x. matrix_inv A ** x))
        ==> invertible B`;;

let INVERTIBLE_NEARBY = `!A:real^N^N.
        invertible A
        ==> ?e. &0 < e /\ !B. onorm(\x. (B - A) ** x) < e ==> invertible B`;;

(* ------------------------------------------------------------------------- *)
(* Cramer's rule.                                                            *)
(* ------------------------------------------------------------------------- *)

let CRAMER_LEMMA_TRANSP = `!A:real^N^N x:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i. if i = k
                           then vsum(1..dimindex(:N)) (\i. x$i % row i A)
                           else row i A):real^N^N) =
            x$k * det A`;;

let CRAMER_LEMMA = `!A:real^N^N x:real^N.
        1 <= k /\ k <= dimindex(:N)
        ==> det((lambda i j. if j = k then (A**x)$i else A$i$j):real^N^N) =
            x$k * det(A)`;;

let CRAMER = `!A:real^N^N x b.
        ~(det(A) = &0)
        ==> (A ** x = b <=>
             x = lambda k.
                   det((lambda i j. if j = k then b$i else A$i$j):real^N^N) /
                   det(A))`;;

(* ------------------------------------------------------------------------- *)
(* Variants of Cramer's rule for matrix-matrix multiplication.               *)
(* ------------------------------------------------------------------------- *)

let CRAMER_MATRIX_LEFT = `!A:real^N^N X:real^N^N B:real^N^N.
        ~(det A = &0)
        ==> (X ** A = B <=>
             X = lambda k l.
                   det((lambda i j. if j = l then B$k$i else A$j$i):real^N^N) /
                   det A)`;;

let CRAMER_MATRIX_RIGHT = `!A:real^N^N X:real^N^N B:real^N^N.
        ~(det A = &0)
        ==> (A ** X = B <=>
             X = lambda k l.
                   det((lambda i j. if j = k then B$i$l else A$i$j):real^N^N) /
                   det A)`;;

let CRAMER_MATRIX_RIGHT_INVERSE = `!A:real^N^N A':real^N^N.
        A ** A' = mat 1 <=>
        ~(det A = &0) /\
        A' = lambda k l.
                det((lambda i j. if j = k then if i = l then &1 else &0
                                 else A$i$j):real^N^N) /
                det A`;;

let CRAMER_MATRIX_LEFT_INVERSE = `!A:real^N^N A':real^N^N.
        A' ** A = mat 1 <=>
        ~(det A = &0) /\
        A' = lambda k l.
                det((lambda i j. if j = l then if i = k then &1 else &0
                                 else A$j$i):real^N^N) /
                det A`;;

(* ------------------------------------------------------------------------- *)
(* Cofactors and their relationship to inverse matrices.                     *)
(* ------------------------------------------------------------------------- *)

let cofactor = new_definition
  `(cofactor:real^N^N->real^N^N) A =
        lambda i j. det((lambda k l. if k = i /\ l = j then &1
                                     else if k = i \/ l = j then &0
                                     else A$k$l):real^N^N)`;;

let COFACTOR_TRANSP = `!A:real^N^N. cofactor(transp A) = transp(cofactor A)`;;

let COFACTOR_COLUMN = `!A:real^N^N.
        cofactor A =
        lambda i j. det((lambda k l. if l = j then if k = i then &1 else &0
                                     else A$k$l):real^N^N)`;;

let COFACTOR_ROW = `!A:real^N^N.
        cofactor A =
        lambda i j. det((lambda k l. if k = i then if l = j then &1 else &0
                                     else A$k$l):real^N^N)`;;

let MATRIX_RIGHT_INVERSE_COFACTOR = `!A:real^N^N A':real^N^N.
        A ** A' = mat 1 <=>
        ~(det A = &0) /\ A' = inv(det A) %% transp(cofactor A)`;;

let MATRIX_LEFT_INVERSE_COFACTOR = `!A:real^N^N A':real^N^N.
        A' ** A = mat 1 <=>
        ~(det A = &0) /\ A' = inv(det A) %% transp(cofactor A)`;;

let MATRIX_INV_COFACTOR = `!A. ~(det A = &0) ==> matrix_inv A = inv(det A) %% transp(cofactor A)`;;

let COFACTOR_MATRIX_INV = `!A:real^N^N. ~(det A = &0) ==> cofactor A = det(A) %% transp(matrix_inv A)`;;

let COFACTOR_I = `cofactor(mat 1:real^N^N) = mat 1`;;

let DET_COFACTOR_EXPANSION = `!A:real^N^N i.
        1 <= i /\ i <= dimindex(:N)
        ==> det A = sum (1..dimindex(:N))
                        (\j. A$i$j * (cofactor A)$i$j)`;;

let MATRIX_MUL_RIGHT_COFACTOR = `!A:real^N^N. A ** transp(cofactor A) = det(A) %% mat 1`;;

let MATRIX_MUL_LEFT_COFACTOR = `!A:real^N^N. transp(cofactor A) ** A = det(A) %% mat 1`;;

let COFACTOR_CMUL = `!A:real^N^N c. cofactor(c %% A) = c pow (dimindex(:N) - 1) %% cofactor A`;;

let COFACTOR_0 = `cofactor(mat 0:real^N^N) = if dimindex(:N) = 1 then mat 1 else mat 0`;;

(* ------------------------------------------------------------------------- *)
(* Explicit formulas for low dimensions.                                     *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_1 = `product(1..1) f = f(1)`;;

let PRODUCT_2 = `!t. product(1..2) t = t(1) * t(2)`;;

let PRODUCT_3 = `!t. product(1..3) t = t(1) * t(2) * t(3)`;;

let PRODUCT_4 = `!t. product(1..4) t = t(1) * t(2) * t(3) * t(4)`;;

let DET_1_GEN = `!A:real^N^N. dimindex(:N) = 1 ==> det A = A$1$1`;;

let DET_1 = `!A:real^1^1. det A = A$1$1`;;

let DET_2 = `!A:real^2^2. det A = A$1$1 * A$2$2 - A$1$2 * A$2$1`;;

let DET_3 = `!A:real^3^3.
        det(A) = A$1$1 * A$2$2 * A$3$3 +
                 A$1$2 * A$2$3 * A$3$1 +
                 A$1$3 * A$2$1 * A$3$2 -
                 A$1$1 * A$2$3 * A$3$2 -
                 A$1$2 * A$2$1 * A$3$3 -
                 A$1$3 * A$2$2 * A$3$1`;;

let DET_4 = `!A:real^4^4.
        det(A) = A$1$1 * A$2$2 * A$3$3 * A$4$4 +
                 A$1$1 * A$2$3 * A$3$4 * A$4$2 +
                 A$1$1 * A$2$4 * A$3$2 * A$4$3 +
                 A$1$2 * A$2$1 * A$3$4 * A$4$3 +
                 A$1$2 * A$2$3 * A$3$1 * A$4$4 +
                 A$1$2 * A$2$4 * A$3$3 * A$4$1 +
                 A$1$3 * A$2$1 * A$3$2 * A$4$4 +
                 A$1$3 * A$2$2 * A$3$4 * A$4$1 +
                 A$1$3 * A$2$4 * A$3$1 * A$4$2 +
                 A$1$4 * A$2$1 * A$3$3 * A$4$2 +
                 A$1$4 * A$2$2 * A$3$1 * A$4$3 +
                 A$1$4 * A$2$3 * A$3$2 * A$4$1 -
                 A$1$1 * A$2$2 * A$3$4 * A$4$3 -
                 A$1$1 * A$2$3 * A$3$2 * A$4$4 -
                 A$1$1 * A$2$4 * A$3$3 * A$4$2 -
                 A$1$2 * A$2$1 * A$3$3 * A$4$4 -
                 A$1$2 * A$2$3 * A$3$4 * A$4$1 -
                 A$1$2 * A$2$4 * A$3$1 * A$4$3 -
                 A$1$3 * A$2$1 * A$3$4 * A$4$2 -
                 A$1$3 * A$2$2 * A$3$1 * A$4$4 -
                 A$1$3 * A$2$4 * A$3$2 * A$4$1 -
                 A$1$4 * A$2$1 * A$3$2 * A$4$3 -
                 A$1$4 * A$2$2 * A$3$3 * A$4$1 -
                 A$1$4 * A$2$3 * A$3$1 * A$4$2`;;

let COFACTOR_1_GEN = `!A:real^N^N. dimindex(:N) = 1 ==> cofactor A = mat 1`;;

let COFACTOR_1 = `!A:real^1^1. cofactor A = mat 1`;;

(* ------------------------------------------------------------------------- *)
(* Disjoint or subset-related halfspaces and hyperplanes are parallel.       *)
(* ------------------------------------------------------------------------- *)

let DISJOINT_HYPERPLANES_IMP_COLLINEAR = `!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}`;;

let DISJOINT_HALFSPACES_IMP_COLLINEAR = `(!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x < c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x <= c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x = c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x >= c} {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        DISJOINT {x | a dot x > c} {x | b dot x > d}
        ==> collinear {vec 0, a, b})`;;

let SUBSET_HALFSPACES_IMP_COLLINEAR = `(!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x < c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x <= c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x = c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x >= c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x < d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x <= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x = d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x >= d}
        ==> collinear {vec 0, a, b}) /\
   (!a b:real^N c d.
        {x | a dot x > c} SUBSET {x | b dot x > d}
        ==> collinear {vec 0, a, b})`;;

let SUBSET_HYPERPLANES = `!a b a' b'.
        {x | a dot x = b} SUBSET {x | a' dot x = b'} <=>
        {x | a dot x = b} = {} \/ {x | a' dot x = b'} = (:real^N) \/
        {x | a dot x = b} = {x | a' dot x = b'}`;;

(* ------------------------------------------------------------------------- *)
(* Existence of the characteristic polynomial.                               *)
(* ------------------------------------------------------------------------- *)

let EIGENVALUES_CHARACTERISTIC_ALT = `!A:real^N^N c.
        (?v. ~(v = vec 0) /\ A ** v = c % v) <=> det(A - c %% mat 1) = &0`;;

let EIGENVALUES_CHARACTERISTIC = `!A:real^N^N c.
        (?v. ~(v = vec 0) /\ A ** v = c % v) <=> det(c %% mat 1 - A) = &0`;;

let INVERTIBLE_EIGENVALUES = `!A:real^N^N.
        invertible(A) <=> !c v. A ** v = c % v /\ ~(v = vec 0) ==> ~(c = &0)`;;

let CHARACTERISTIC_POLYNOMIAL = `!A:real^N^N.
        ?a. a(dimindex(:N)) = &1 /\
            !x. det(x %% mat 1 - A) =
                sum (0..dimindex(:N)) (\i. a i * x pow i)`;;

let FINITE_EIGENVALUES = `!A:real^N^N. FINITE {c | ?v. ~(v = vec 0) /\ A ** v = c % v}`;;

(* ------------------------------------------------------------------------- *)
(* Grassmann-Plucker relations for n = 2, n = 3 and n = 4.                   *)
(* I have a proof of the general n case but the proof is a bit long and the  *)
(* result doesn't seem generally useful enough to go in the main theories.   *)
(* ------------------------------------------------------------------------- *)

let GRASSMANN_PLUCKER_2 = `!x1 x2 y1 y2:real^2.
        det(vector[x1;x2]) * det(vector[y1;y2]) =
          det(vector[y1;x2]) * det(vector[x1;y2]) +
          det(vector[y2;x2]) * det(vector[y1;x1])`;;

let GRASSMANN_PLUCKER_3 = `!x1 x2 x3 y1 y2 y3:real^3.
        det(vector[x1;x2;x3]) * det(vector[y1;y2;y3]) =
          det(vector[y1;x2;x3]) * det(vector[x1;y2;y3]) +
          det(vector[y2;x2;x3]) * det(vector[y1;x1;y3]) +
          det(vector[y3;x2;x3]) * det(vector[y1;y2;x1])`;;

let GRASSMANN_PLUCKER_4 = `!x1 x2 x3 x4:real^4 y1 y2 y3 y4:real^4.
        det(vector[x1;x2;x3;x4]) * det(vector[y1;y2;y3;y4]) =
          det(vector[y1;x2;x3;x4]) * det(vector[x1;y2;y3;y4]) +
          det(vector[y2;x2;x3;x4]) * det(vector[y1;x1;y3;y4]) +
          det(vector[y3;x2;x3;x4]) * det(vector[y1;y2;x1;y4]) +
          det(vector[y4;x2;x3;x4]) * det(vector[y1;y2;y3;x1])`;;

(* ------------------------------------------------------------------------- *)
(* Determinants of integer matrices.                                         *)
(* ------------------------------------------------------------------------- *)

let INTEGER_PRODUCT = `!f s. (!x. x IN s ==> integer(f x)) ==> integer(product s f)`;;

let INTEGER_SIGN = `!p. integer(sign p)`;;

let INTEGER_DET = `!M:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N)
               ==> integer(M$i$j))
        ==> integer(det M)`;;

(* ------------------------------------------------------------------------- *)
(* Diagonal matrices (for arbitrary rectangular matrix, not just square).    *)
(* ------------------------------------------------------------------------- *)

let diagonal_matrix = new_definition
 `diagonal_matrix(A:real^N^M) <=>
        !i j. 1 <= i /\ i <= dimindex(:M) /\
              1 <= j /\ j <= dimindex(:N) /\
              ~(i = j)
              ==> A$i$j = &0`;;

let DIAGONAL_MATRIX = `!A:real^N^N.
     diagonal_matrix A <=> A = (lambda i j. if i = j then A$i$j else &0)`;;

let DIAGONAL_MATRIX_MAT = `!m. diagonal_matrix(mat m:real^N^N)`;;

let TRANSP_DIAGONAL_MATRIX = `!A:real^N^N. diagonal_matrix A ==> transp A = A`;;

let DIAGONAL_IMP_SYMMETRIC_MATRIX = `!A:real^N^N. diagonal_matrix A ==> symmetric_matrix A`;;

let DIAGONAL_MATRIX_ADD = `!A B:real^N^M.
        diagonal_matrix A /\ diagonal_matrix B
        ==> diagonal_matrix(A + B)`;;

let DIAGONAL_MATRIX_CMUL = `!A:real^N^M c.
        diagonal_matrix A ==> diagonal_matrix(c %% A)`;;

let MATRIX_MUL_DIAGONAL = `!A:real^N^N B:real^N^N.
        diagonal_matrix A /\ diagonal_matrix B
        ==> A ** B = lambda i j. A$i$j * B$i$j`;;

let DIAGONAL_MATRIX_MUL_COMPONENT = `!A:real^N^N B:real^N^N i j.
        diagonal_matrix A /\ diagonal_matrix B /\
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> (A ** B)$i$j = A$i$j * B$i$j`;;

let DIAGONAL_MATRIX_MUL = `!A:real^N^N B:real^N^N.
        diagonal_matrix A /\ diagonal_matrix B
        ==> diagonal_matrix(A ** B)`;;

let DIAGONAL_MATRIX_MUL_EQ = `!A:real^M^N B:real^N^M.
        diagonal_matrix (A ** B) <=>
        pairwise (\i j. orthogonal (row i A) (column j B)) (1..dimindex(:N))`;;

let DIAGONAL_MATRIX_INV_EXPLICIT = `!A:real^N^N. diagonal_matrix A ==> matrix_inv A = lambda i j. inv(A$i$j)`;;

let DIAGONAL_MATRIX_INV_COMPONENT = `!A:real^N^N i j.
        diagonal_matrix A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (matrix_inv A)$i$j = inv(A$i$j)`;;

let DIAGONAL_MATRIX_INV = `!A:real^N^N. diagonal_matrix(matrix_inv A) <=> diagonal_matrix A`;;

let DET_DIAGONAL = `!A:real^N^N.
        diagonal_matrix A
        ==> det(A) = product(1..dimindex(:N)) (\i. A$i$i)`;;

let INVERTIBLE_DIAGONAL_MATRIX = `!D:real^N^N.
        diagonal_matrix D
        ==> (invertible D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> ~(D$i$i = &0))`;;

let COMMUTING_WITH_DIAGONAL_MATRIX = `!A D:real^N^N.
        diagonal_matrix D
        ==> (A ** D = D ** A <=>
             !i j. 1 <= i /\ i <= dimindex(:N) /\
                   1 <= j /\ j <= dimindex(:N)
                   ==> A$i$j = &0 \/ D$i$i = D$j$j)`;;

let RANK_DIAGONAL_MATRIX = `!A:real^N^N.
        diagonal_matrix A
        ==> rank A = CARD {i | i IN 1..dimindex(:N) /\ ~(A$i$i = &0)}`;;

let ONORM_DIAGONAL_MATRIX = `!A:real^N^N.
       diagonal_matrix A
       ==> onorm(\x. A ** x) = sup {abs(A$i$i) | 1 <= i /\ i <= dimindex(:N)}`;;

(* ------------------------------------------------------------------------- *)
(* Positive semidefinite matrices.                                           *)
(* ------------------------------------------------------------------------- *)

let positive_semidefinite = new_definition
 `positive_semidefinite(A:real^N^N) <=>
    symmetric_matrix A /\ !x. &0 <= x dot (A ** x)`;;

let POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX = `!A:real^N^N. positive_semidefinite A ==> symmetric_matrix A`;;

let POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC = `!A:real^N^N. positive_semidefinite A ==> transp A = A`;;

let POSITIVE_SEMIDEFINITE_ADD = `!A B:real^N^N.
        positive_semidefinite A /\ positive_semidefinite B
        ==> positive_semidefinite(A + B)`;;

let POSITIVE_SEMIDEFINITE_CMUL = `!c A:real^N^N.
        positive_semidefinite A /\ &0 <= c
        ==> positive_semidefinite(c %% A)`;;

let POSITIVE_SEMIDEFINITE_TRANSP = `!A:real^N^N. positive_semidefinite(transp A) <=> positive_semidefinite A`;;

let POSITIVE_SEMIDEFINITE_COVARIANCE = `!A:real^N^M. positive_semidefinite(transp A ** A)`;;

let POSITIVE_SEMIDEFINITE_SIMILAR = `!A B:real^N^M.
        positive_semidefinite A
        ==> positive_semidefinite(transp B ** A ** B)`;;

let POSITIVE_SEMIDEFINITE_SIMILAR_EQ = `!A B:real^N^N.
        invertible B
        ==> (positive_semidefinite (transp B ** A ** B) <=>
             positive_semidefinite A)`;;

let POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX = `!D:real^N^N.
        diagonal_matrix D /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i)
        ==> positive_semidefinite D`;;

let POSITIVE_SEMIDEFINITE_DIAGONAL_MATRIX_EQ = `!D:real^N^N.
        diagonal_matrix D
        ==> (positive_semidefinite D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> &0 <= D$i$i)`;;

let DIAGONAL_POSITIVE_SEMIDEFINITE = `!A:real^N^N i.
        positive_semidefinite A /\ 1 <= i /\ i <= dimindex(:N)
        ==> &0 <= A$i$i`;;

let TRACE_POSITIVE_SEMIDEFINITE = `!A:real^N^N. positive_semidefinite A ==> &0 <= trace A`;;

let TRACE_LE_MUL_SQUARES = `!A B:real^N^N.
        symmetric_matrix A /\ symmetric_matrix B
        ==> trace((A ** B) ** (A ** B)) <= trace((A ** A) ** (B ** B))`;;

let POSITIVE_SEMIDEFINITE_ZERO_FORM = `!A:real^N^N. positive_semidefinite A /\ x dot (A ** x) = &0
                ==> A ** x = vec 0`;;

let POSITIVE_SEMIDEFINITE_ZERO_FORM_EQ = `!A:real^N^N. positive_semidefinite A
                ==> (x dot (A ** x) = &0 <=> A ** x = vec 0)`;;

let POSITIVE_SEMIDEFINITE_1_GEN = `!A:real^N^N.
        dimindex(:N) = 1 ==> (positive_semidefinite A <=> &0 <= A$1$1)`;;

let POSITIVE_SEMIDEFINITE_1 = `!A:real^1^1. positive_semidefinite A <=> &0 <= A$1$1`;;

let POSITIVE_SEMIDEFINITE_SUBMATRIX_2 = `!A:real^N^N i j.
        positive_semidefinite A /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> positive_semidefinite
              (vector[vector[A$i$i;A$i$j];
                      vector[A$j$i;A$j$j]]:real^2^2)`;;

(* ------------------------------------------------------------------------- *)
(* The Frobenius norm and associated inner product, which turn out to be the *)
(* usual Euclidean versions modulo flattening.                               *)
(* ------------------------------------------------------------------------- *)

let DOT_VECTORIZE = `!A B:real^N^M. vectorize A dot vectorize B = trace(transp A ** B)`;;

let NORM_VECTORIZE_TRANSP = `!A:real^N^M. norm(vectorize(transp A)) = norm(vectorize A)`;;

let COMPATIBLE_NORM_VECTORIZE = `!A:real^N^M x. norm(A ** x) <= norm(vectorize A) * norm x`;;

let ONORM_LE_NORM_VECTORIZE = `!A:real^M^N. onorm(\x. A ** x) <= norm(vectorize A)`;;

let NORM_VECTORIZE_POW_2 = `!A:real^N^M.
    norm(vectorize A) pow 2 = sum(1..dimindex(:M)) (\i. norm(A$i) pow 2)`;;

let NORM_VECTORIZE_MUL_LE = `!A:real^N^P B:real^M^N.
    norm(vectorize(A ** B)) <= norm(vectorize A) * norm(vectorize B)`;;

let NORM_VECTORIZE_HADAMARD_LE = `!A:real^N^M B:real^N^M.
        norm(vectorize((lambda i j. A$i$j * B$i$j):real^N^M))
        <= norm(vectorize A) * norm(vectorize B)`;;

let TRACE_COVARIANCE_POS_LE = `!A:real^M^N. &0 <= trace(transp A ** A)`;;

let TRACE_COVARIANCE_EQ_0 = `!A:real^M^N. trace(transp A ** A) = &0 <=> A = mat 0`;;

let TRACE_COVARIANCE_POS_LT = `!A:real^M^N. &0 < trace(transp A ** A) <=> ~(A = mat 0)`;;

let TRACE_COVARIANCE_CAUCHY_SCHWARZ = `!A B:real^M^N.
        trace(transp A ** B)
         <= sqrt(trace(transp A ** A)) * sqrt(trace(transp B ** B))`;;

let TRACE_COVARIANCE_CAUCHY_SCHWARZ_ABS = `!A B:real^M^N.
        abs(trace(transp A ** B))
         <= sqrt(trace(transp A ** A)) * sqrt(trace(transp B ** B))`;;

let TRACE_COVARIANCE_CAUCHY_SCHWARZ_SQUARE = `!A B:real^M^N.
        trace(transp A ** B) pow 2
        <= trace(transp A ** A) * trace(transp B ** B)`;;

(* ------------------------------------------------------------------------- *)
(* Positive definite matrices.                                               *)
(* ------------------------------------------------------------------------- *)

let positive_definite = new_definition
 `positive_definite(A:real^N^N) <=>
         symmetric_matrix A /\ !x. ~(x = vec 0) ==> &0 < x dot (A ** x)`;;

let POSITIVE_DEFINITE_IMP_SYMMETRIC_MATRIX = `!A:real^N^N. positive_definite A ==> symmetric_matrix A`;;

let POSITIVE_DEFINITE_IMP_SYMMETRIC = `!A:real^N^N. positive_definite A ==> transp A = A`;;

let POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE = `!A:real^N^N.
        positive_definite A <=> positive_semidefinite A /\ invertible A`;;

let POSITIVE_DEFINITE_SIMILAR_EQ = `!A B:real^N^N.
        positive_definite(transp B ** A ** B) <=>
        invertible B /\ positive_definite A`;;

let POSITIVE_DEFINITE_1_GEN = `!A:real^N^N.
        dimindex(:N) = 1 ==> (positive_definite A <=> &0 < A$1$1)`;;

let POSITIVE_DEFINITE_1 = `!A:real^1^1. positive_definite A <=> &0 < A$1$1`;;

let POSITIVE_DEFINITE_IMP_INVERTIBLE = `!A:real^N^N. positive_definite A ==> invertible A`;;

let POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE = `!A:real^N^N. positive_definite A ==> positive_semidefinite A`;;

let POSITIVE_SEMIDEFINITE_POSITIVE_DEFINITE_ADD = `!A B:real^N^N.
        positive_semidefinite A /\ positive_definite B
        ==> positive_definite(A + B)`;;

let POSITIVE_DEFINITE_POSITIVE_SEMIDEFINITE_ADD = `!A B:real^N^N.
        positive_definite A /\ positive_semidefinite B
        ==> positive_definite(A + B)`;;

let POSITIVE_DEFINITE_ADD = `!A B:real^N^N.
        positive_definite A /\ positive_definite B
        ==> positive_definite(A + B)`;;

let POSITIVE_DEFINITE_CMUL = `!c A:real^N^N.
        positive_definite A /\ &0 < c
        ==> positive_definite(c %% A)`;;

let NEARBY_POSITIVE_DEFINITE_MATRIX_GEN = `!A:real^N^N B x.
        positive_semidefinite A /\ positive_definite B /\ &0 < x
        ==> positive_definite(A + x %% B)`;;

let POSITIVE_DEFINITE_TRANSP = `!A:real^N^N. positive_definite(transp A) <=> positive_definite A`;;

let POSITIVE_DEFINITE_COVARIANCE = `!A:real^N^N. positive_definite(transp A ** A) <=> invertible A`;;

let POSITIVE_DEFINITE_SIMILAR = `!A B:real^N^N.
        positive_definite A /\ invertible B
        ==> positive_definite(transp B ** A ** B)`;;

let POSITIVE_DEFINITE_DIAGONAL_MATRIX = `!D:real^N^N.
        diagonal_matrix D /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> &0 < D$i$i)
        ==> positive_definite D`;;

let POSITIVE_DEFINITE_DIAGONAL_MATRIX_EQ = `!D:real^N^N.
        diagonal_matrix D
        ==> (positive_definite D <=>
             !i. 1 <= i /\ i <= dimindex(:N) ==> &0 < D$i$i)`;;

let DIAGONAL_POSITIVE_DEFINITE = `!A:real^N^N i.
        positive_definite A /\ 1 <= i /\ i <= dimindex(:N)
        ==> &0 < A$i$i`;;

let TRACE_POSITIVE_DEFINITE = `!A:real^N^N. positive_definite A ==> &0 < trace A`;;

let POSITIVE_DEFINITE_MAT = `!m. positive_definite(mat m:real^N^N) <=> 0 < m`;;

let POSITIVE_DEFINITE_ID = `positive_definite(mat 1:real^N^N)`;;

let POSITIVE_SEMIDEFINITE_MAT = `!m. positive_semidefinite(mat m:real^N^N)`;;

let NEARBY_POSITIVE_DEFINITE_MATRIX = `!A:real^N^N x.
      positive_semidefinite A /\ &0 < x ==> positive_definite(A + x %% mat 1)`;;

let POSITIVE_SEMIDEFINITE_ANTISYM = `!A:real^N^N. positive_semidefinite A /\ positive_semidefinite(--A) <=>
                A = mat 0`;;

let LOEWNER_ORDER_ANTISYM = `!(A:real^N^N) B.
        positive_semidefinite(A - B) /\ positive_semidefinite(B - A) <=>
        A = B`;;

(* ------------------------------------------------------------------------- *)
(* Hadamard's inequality.                                                    *)
(* ------------------------------------------------------------------------- *)

let HADAMARD_INEQUALITY_ROW = `!A:real^N^N. abs(det A) <= product(1..dimindex(:N)) (\i. norm(row i A))`;;

let HADAMARD_INEQUALITY_COLUMN = `!A:real^N^N. abs(det A) <= product(1..dimindex(:N)) (\i. norm(column i A))`;;

(* ------------------------------------------------------------------------- *)
(* Orthogonality of a transformation and matrix.                             *)
(* ------------------------------------------------------------------------- *)

let orthogonal_transformation = new_definition
 `orthogonal_transformation(f:real^N->real^N) <=>
        linear f /\ !v w. f(v) dot f(w) = v dot w`;;

let ORTHOGONAL_TRANSFORMATION = `!f. orthogonal_transformation f <=> linear f /\ !v. norm(f v) = norm(v)`;;

let ORTHOGONAL_ORTHOGONAL_TRANSFORMATION = `!f x y:real^N.
        orthogonal_transformation f
        ==> (orthogonal (f x) (f y) <=> orthogonal x y)`;;

let ORTHOGONAL_TRANSFORMATION_COMPOSE = `!f g. orthogonal_transformation f /\ orthogonal_transformation g
         ==> orthogonal_transformation(f o g)`;;

let ORTHOGONAL_TRANSFORMATION_NEG = `!f:real^N->real^N.
     orthogonal_transformation(\x. --(f x)) <=> orthogonal_transformation f`;;

let ORTHOGONAL_TRANSFORMATION_LINEAR = `!f:real^N->real^N. orthogonal_transformation f ==> linear f`;;

let ORTHOGONAL_TRANSFORMATION_INJECTIVE = `!f:real^N->real^N.
        orthogonal_transformation f ==> !x y. f x = f y ==> x = y`;;

let ORTHOGONAL_TRANSFORMATION_SURJECTIVE = `!f:real^N->real^N.
        orthogonal_transformation f ==> !y. ?x. f x = y`;;

let orthogonal_matrix = new_definition
 `orthogonal_matrix(Q:real^N^N) <=>
      transp(Q) ** Q = mat 1 /\ Q ** transp(Q) = mat 1`;;

let ORTHOGONAL_MATRIX = `orthogonal_matrix(Q:real^N^N) <=> transp(Q) ** Q = mat 1`;;

let ORTHOGONAL_MATRIX_ALT = `!A:real^N^N. orthogonal_matrix A <=> A ** transp A = mat 1`;;

let ORTHOGONAL_MATRIX_TRANSP = `!A:real^N^N. orthogonal_matrix(transp A) <=> orthogonal_matrix A`;;

let ORTHOGONAL_MATRIX_TRANSP_LMUL = `!P:real^N^N. orthogonal_matrix P ==> transp P ** P = mat 1`;;

let ORTHOGONAL_MATRIX_TRANSP_RMUL = `!P:real^N^N. orthogonal_matrix P ==> P ** transp P = mat 1`;;

let NORM_VECTORIZE_ORTHOGONAL_MATRIX_RMUL = `!A:real^N^N P:real^N^N.
       orthogonal_matrix P ==> norm(vectorize(A ** P)) = norm(vectorize A)`;;

let NORM_VECTORIZE_ORTHOGONAL_MATRIX_LMUL = `!A:real^N^N P:real^N^N.
       orthogonal_matrix P ==> norm(vectorize(P ** A)) = norm(vectorize A)`;;

let ORTHOGONAL_MATRIX_ID = `orthogonal_matrix(mat 1)`;;

let ORTHOGONAL_MATRIX_MUL = `!A B. orthogonal_matrix A /\ orthogonal_matrix B
         ==> orthogonal_matrix(A ** B)`;;

let ORTHOGONAL_TRANSFORMATION_MATRIX = `!f:real^N->real^N.
     orthogonal_transformation f <=> linear f /\ orthogonal_matrix(matrix f)`;;

let ORTHOGONAL_MATRIX_TRANSFORMATION = `!A:real^N^N. orthogonal_matrix A <=> orthogonal_transformation(\x. A ** x)`;;

let ORTHOGONAL_MATRIX_MATRIX = `!f:real^N->real^N.
    orthogonal_transformation f ==> orthogonal_matrix(matrix f)`;;

let ORTHOGONAL_MATRIX_NORM_EQ = `!A. orthogonal_matrix A <=> !x. norm(A ** x) = norm x`;;

let ORTHOGONAL_MATRIX_NORM = `!A x:real^N. orthogonal_matrix A ==> norm(A ** x) = norm x`;;

let DET_ORTHOGONAL_MATRIX = `!Q. orthogonal_matrix Q ==> det(Q) = &1 \/ det(Q) = -- &1`;;

let ORTHOGONAL_MATRIX_IMP_INVERTIBLE = `!A:real^N^N. orthogonal_matrix A ==> invertible A`;;

let MATRIX_MUL_LTRANSP_DOT_COLUMN = `!A:real^N^M. transp A ** A = (lambda i j. (column i A) dot (column j A))`;;

let MATRIX_MUL_RTRANSP_DOT_ROW = `!A:real^N^M. A ** transp A = (lambda i j. (row i A) dot (row j A))`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS = `!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> orthogonal (column i A) (column j A))`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS = `!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> orthogonal (row i A) (row j A))`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED = `!A:real^N^N.
        orthogonal_matrix A <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise (\i j. orthogonal (row i A) (row j A)) (1..dimindex(:N))`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_PAIRWISE = `!A:real^N^N.
        orthogonal_matrix A <=>
        CARD(rows A) = dimindex(:N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise orthogonal (rows A)`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_SPAN = `!A:real^N^N.
        orthogonal_matrix A <=>
        span(rows A) = (:real^N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(row i A) = &1) /\
        pairwise orthogonal (rows A)`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_INDEXED = `!A:real^N^N.
      orthogonal_matrix A <=>
      (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
      pairwise (\i j. orthogonal (column i A) (column j A)) (1..dimindex(:N))`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_PAIRWISE = `!A:real^N^N.
        orthogonal_matrix A <=>
        CARD(columns A) = dimindex(:N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        pairwise orthogonal (columns A)`;;

let ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS_SPAN = `!A:real^N^N.
        orthogonal_matrix A <=>
        span(columns A) = (:real^N) /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> norm(column i A) = &1) /\
        pairwise orthogonal (columns A)`;;

let ORTHOGONAL_MATRIX_2 = `!A:real^2^2. orthogonal_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                A$1$2 pow 2 + A$2$2 pow 2 = &1 /\
                A$1$1 * A$1$2 + A$2$1 * A$2$2 = &0`;;

let ORTHOGONAL_MATRIX_2_ALT = `!A:real^2^2. orthogonal_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                (A$1$1 = A$2$2 /\ A$1$2 = --(A$2$1) \/
                 A$1$1 = --(A$2$2) /\ A$1$2 = A$2$1)`;;

let ORTHOGONAL_MATRIX_INV = `!A:real^N^N. orthogonal_matrix A ==> matrix_inv A = transp A`;;

let ORTHOGONAL_MATRIX_INV_EQ = `!A:real^N^N. orthogonal_matrix(matrix_inv A) <=> orthogonal_matrix A`;;

let ORTHOGONAL_TRANSFORMATION_ORTHOGONAL_EIGENVECTORS = `!f:real^N->real^N v w a b.
        orthogonal_transformation f /\ f v = a % v /\ f w = b % w /\ ~(a = b)
        ==> orthogonal v w`;;

let ORTHOGONAL_MATRIX_ORTHOGONAL_EIGENVECTORS = `!A:real^N^N v w a b.
        orthogonal_matrix A /\ A ** v = a % v /\ A ** w = b % w /\ ~(a = b)
        ==> orthogonal v w`;;

let ORTHOGONAL_TRANSFORMATION_ID = `orthogonal_transformation(\x. x)`;;

let ORTHOGONAL_TRANSFORMATION_I = `orthogonal_transformation I`;;

let ORTHOGONAL_TRANSFORMATION_NEGATION = `orthogonal_transformation(--)`;;

let ORTHOGONAL_TRANSFORMATION_1_GEN = `!f:real^N->real^N.
        dimindex(:N) = 1
        ==> (orthogonal_transformation f <=> f = I \/ f = (--))`;;

let ORTHOGONAL_MATRIX_1 = `!m:real^N^N.
        dimindex(:N) = 1
        ==> (orthogonal_matrix m <=> m = mat 1 \/ m = --mat 1)`;;

let MATRIX_INV_ORTHOGONAL_LMUL = `!U A:real^M^N.
        orthogonal_matrix U
        ==> matrix_inv(U ** A) = matrix_inv A ** matrix_inv U`;;

let MATRIX_INV_ORTHOGONAL_RMUL = `!U A:real^M^N.
        orthogonal_matrix U
        ==> matrix_inv(A ** U) = matrix_inv U ** matrix_inv A`;;

let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_LEFT = `!f:real^N->real^N.
        orthogonal_transformation f <=> linear f /\ adjoint f o f = I`;;

let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT_RIGHT = `!f:real^N->real^N.
        orthogonal_transformation f <=> linear f /\ f o adjoint f = I`;;

let ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT = `!f:real^N->real^N.
        orthogonal_transformation f <=>
        linear f /\ adjoint f o f = I /\ f o adjoint f = I`;;

let ORTHOGONAL_TRANSFORMATION_ADJOINT = `!f:real^N->real^N.
        orthogonal_transformation f ==> orthogonal_transformation(adjoint f)`;;

let ORTHOGONAL_TRANSFORMATION_ADJOINT_EQ =
 (`!f:real^N->real^N.
        linear f
        ==> (orthogonal_transformation(adjoint f) <=>
             orthogonal_transformation f)`,
  MESON_TAC[ORTHOGONAL_TRANSFORMATION_ADJOINT; ADJOINT_LINEAR;
            ADJOINT_ADJOINT]);;

let ONORM_ORTHOGONAL_TRANSFORMATION = `!f:real^N->real^N. orthogonal_transformation f ==> onorm f = &1`;;

let ONORM_ORTHOGONAL_MATRIX = `!A:real^N^N. orthogonal_matrix A ==> onorm(\x. A ** x) = &1`;;

(* ------------------------------------------------------------------------- *)
(* Linearity of scaling, and hence isometry, that preserves origin.          *)
(* ------------------------------------------------------------------------- *)

let SCALING_LINEAR = `!f:real^M->real^N c.
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = c * dist(x,y))
        ==> linear(f)`;;

let ISOMETRY_LINEAR = `!f:real^M->real^N.
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = dist(x,y))
        ==> linear(f)`;;

let ISOMETRY_IMP_AFFINITY = `!f:real^M->real^N.
        (!x y. dist(f x,f y) = dist(x,y))
        ==> ?h. linear h /\ !x. f(x) = f(vec 0) + h(x)`;;

(* ------------------------------------------------------------------------- *)
(* An orthogonality-preserving linear map is a similarity.                   *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONALITY_PRESERVING_IMP_SCALING = `!f:real^M->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y))
        ==> ?c. &0 <= c /\ !x. norm(f x) = c * norm(x)`;;

let ORTHOGONALITY_PRESERVING_EQ_SIMILARITY_ALT,
    ORTHOGONALITY_PRESERVING_EQ_SIMILARITY =
  (CONJ_PAIR o prove)
 (`(!f:real^N->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y)) <=>
        ?c g. &0 <= c /\ orthogonal_transformation g /\ f = \z. c % g z) /\
   (!f:real^N->real^N.
        linear f /\ (!x y. orthogonal x y ==> orthogonal (f x) (f y)) <=>
        ?c g. orthogonal_transformation g /\ f = \z. c % g z)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(q ==> r) /\ (r ==> p) /\ (p ==> q)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    STRIP_TAC THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_COMPOSE_CMUL] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MUL; ORTHOGONAL_ORTHOGONAL_TRANSFORMATION];
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONALITY_PRESERVING_IMP_SCALING) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
    ASM_CASES_TAC `c = &0` THENL
     [ASM_SIMP_TAC[REAL_MUL_LZERO; FUN_EQ_THM; NORM_EQ_0] THEN
      DISCH_TAC THEN EXISTS_TAC `\x:real^N. x` THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; ORTHOGONAL_TRANSFORMATION_ID];
      STRIP_TAC THEN EXISTS_TAC `\x. inv(c) % (f:real^N->real^N) x` THEN
      ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; FUN_EQ_THM] THEN
      ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; NORM_MUL; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID; REAL_ABS_INV] THEN
      ASM_REWRITE_TAC[real_abs; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence another formulation of orthogonal transformation.                   *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_ISOMETRY = `!f:real^N->real^N.
        orthogonal_transformation f <=>
        (f(vec 0) = vec 0) /\ (!x y. dist(f x,f y) = dist(x,y))`;;

(* ------------------------------------------------------------------------- *)
(* Can extend an isometry from unit sphere.                                  *)
(* ------------------------------------------------------------------------- *)

let ISOMETRY_SPHERE_EXTEND = `!f:real^N->real^N.
        (!x. norm(x) = &1 ==> norm(f x) = &1) /\
        (!x y. norm(x) = &1 /\ norm(y) = &1 ==> dist(f x,f y) = dist(x,y))
        ==> ?g. orthogonal_transformation g /\
                (!x. norm(x) = &1 ==> g(x) = f(x))`;;

let ORTHOGONAL_TRANSFORMATION_INVERSE_o = `!f:real^N->real^N.
        orthogonal_transformation f
        ==> ?g. orthogonal_transformation g /\ g o f = I /\ f o g = I`;;

let ORTHOGONAL_TRANSFORMATION_INVERSE = `!f:real^N->real^N.
        orthogonal_transformation f
        ==> ?g. orthogonal_transformation g /\
                (!x. g(f x) = x) /\ (!y. f(g y) = y)`;;

let ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_LEFT = `!f g. orthogonal_transformation f ==> onorm(f o g) = onorm g`;;

let ONORM_COMPOSE_ORTHOGONAL_TRANSFORMATION_RIGHT = `!f g. orthogonal_transformation g ==> onorm(f o g) = onorm f`;;

(* ------------------------------------------------------------------------- *)
(* Reading operator norms off eigenvalue bases or diagonalizations.          *)
(* ------------------------------------------------------------------------- *)

let SQNORM_LE_MAX_EIGENVECTOR_SPAN = `!(f:real^N->real^N) b c x l.
        linear f /\
        pairwise orthogonal b /\
        (!x. x IN b ==> f x = c x % x /\ c x pow 2 <= l) /\
        x IN span b
        ==> norm(f x) pow 2 <= l * norm x pow 2`;;

let NORM_LE_MAX_EIGENVECTOR_SPAN = `!(f:real^N->real^N) b c x l.
        linear f /\
        pairwise orthogonal b /\
        (!x. x IN b ==> f x = c x % x /\ abs(c x) <= l) /\
        x IN span b
        ==> norm(f x) <= l * norm x`;;

let ONORM_EQ_MAX_EIGENVECTOR = `!(f:real^N->real^N) b c.
        linear f /\
        pairwise orthogonal b /\
        span b = (:real^N) /\
        ~(vec 0 IN b) /\
        (!x. x IN b ==> f x = c x % x)
        ==> onorm f = sup {abs(c x) | x IN b}`;;

let ONORM_ORTHOGONAL_MATRIX_MUL_LEFT = `!(A:real^N^N) (P:real^N^N).
        orthogonal_matrix P ==> onorm (\x. (P ** A) ** x) = onorm(\x. A ** x)`;;

let ONORM_ORTHOGONAL_MATRIX_MUL_RIGHT = `!(A:real^N^N) (P:real^N^N).
        orthogonal_matrix P ==> onorm (\x. (A ** P) ** x) = onorm(\x. A ** x)`;;

let ONORM_DIAGONALIZED_MATRIX = `!(A:real^N^N) D P.
      orthogonal_matrix P /\
      diagonal_matrix D /\
      transp P ** D ** P = A
      ==> onorm(\x. A ** x) = sup {abs(D$i$i) | 1 <= i /\ i <= dimindex (:N)}`;;

let ONORM_DIAGONALIZED_COVARIANCE_MATRIX = `!(A:real^N^N) D P.
      orthogonal_matrix P /\
      diagonal_matrix D /\
      transp P ** D ** P = transp A ** A
      ==> onorm(\x. A ** x) =
          sqrt(sup {abs(D$i$i) | 1 <= i /\ i <= dimindex (:N)})`;;

(* ------------------------------------------------------------------------- *)
(* We can find an orthogonal matrix taking any unit vector to any other.     *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_MATRIX_EXISTS_BASIS = `!a:real^N.
        norm(a) = &1
        ==> ?A. orthogonal_matrix A /\ A**(basis 1) = a`;;

let ORTHOGONAL_TRANSFORMATION_EXISTS_1 = `!a b:real^N.
        norm(a) = &1 /\ norm(b) = &1
        ==> ?f. orthogonal_transformation f /\ f a = b`;;

let ORTHOGONAL_TRANSFORMATION_EXISTS = `!a b:real^N.
        norm(a) = norm(b) ==> ?f. orthogonal_transformation f /\ f a = b`;;

(* ------------------------------------------------------------------------- *)
(* Or indeed, taking any subspace to another of suitable dimension.          *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_INTO_SUBSPACE = `!s t:real^N->bool.
        subspace s /\ subspace t /\ dim s <= dim t
        ==> ?f. orthogonal_transformation f /\ IMAGE f s SUBSET t`;;

let ORTHOGONAL_TRANSFORMATION_ONTO_SUBSPACE = `!s t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t
        ==> ?f. orthogonal_transformation f /\ IMAGE f s = t`;;

(* ------------------------------------------------------------------------- *)
(* Rotation, reflection, rotoinversion.                                      *)
(* ------------------------------------------------------------------------- *)

let rotation_matrix = new_definition
 `rotation_matrix Q <=> orthogonal_matrix Q /\ det(Q) = &1`;;

let rotoinversion_matrix = new_definition
 `rotoinversion_matrix Q <=> orthogonal_matrix Q /\ det(Q) = -- &1`;;

let ORTHOGONAL_ROTATION_OR_ROTOINVERSION = `!Q. orthogonal_matrix Q <=> rotation_matrix Q \/ rotoinversion_matrix Q`;;

let ROTATION_MATRIX_1 = `!m:real^N^N.
        dimindex(:N) = 1 ==> (rotation_matrix m <=> m = mat 1)`;;

let ROTOINVERSION_MATRIX_1 = `!m:real^N^N.
        dimindex(:N) = 1 ==> (rotoinversion_matrix m <=> m = --mat 1)`;;

let ROTATION_MATRIX_2 = `!A:real^2^2. rotation_matrix A <=>
                A$1$1 pow 2 + A$2$1 pow 2 = &1 /\
                A$1$1 = A$2$2 /\ A$1$2 = --(A$2$1)`;;

(* ------------------------------------------------------------------------- *)
(* Slightly stronger results giving rotation, but only in >= 2 dimensions.   *)
(* ------------------------------------------------------------------------- *)

let ROTATION_MATRIX_EXISTS_BASIS = `!a:real^N.
        2 <= dimindex(:N) /\ norm(a) = &1
        ==> ?A. rotation_matrix A /\ A**(basis 1) = a`;;

let ROTATION_EXISTS_1 = `!a b:real^N.
        2 <= dimindex(:N) /\ norm(a) = &1 /\ norm(b) = &1
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f a = b`;;

let ROTATION_EXISTS = `!a b:real^N.
        2 <= dimindex(:N) /\ norm(a) = norm(b)
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f a = b`;;

let ROTATION_RIGHTWARD_LINE = `!a:real^N k.
        1 <= k /\ k <= dimindex(:N)
        ==> ?b f. orthogonal_transformation f /\
                  (2 <= dimindex(:N) ==> det(matrix f) = &1) /\
                  f(b % basis k) = a /\
                  &0 <= b`;;

(* ------------------------------------------------------------------------- *)
(* In 3 dimensions, a rotation is indeed about an "axis".                    *)
(* ------------------------------------------------------------------------- *)

let EULER_ROTATION_THEOREM = `!A:real^3^3. rotation_matrix A ==> ?v:real^3. ~(v = vec 0) /\ A ** v = v`;;

let EULER_ROTOINVERSION_THEOREM = `!A:real^3^3.
     rotoinversion_matrix A ==> ?v:real^3. ~(v = vec 0) /\ A ** v = --v`;;

(* ------------------------------------------------------------------------- *)
(* We can always rotate so that a hyperplane is "horizontal".                *)
(* ------------------------------------------------------------------------- *)

let ROTATION_LOWDIM_HORIZONTAL = `!s:real^N->bool.
        dim s < dimindex(:N)
        ==> ?f. orthogonal_transformation f /\ det(matrix f) = &1 /\
               (IMAGE f s) SUBSET {z | z$(dimindex(:N)) = &0}`;;

let ORTHOGONAL_TRANSFORMATION_LOWDIM_HORIZONTAL = `!s:real^N->bool.
        dim s < dimindex(:N)
        ==> ?f. orthogonal_transformation f /\
               (IMAGE f s) SUBSET {z | z$(dimindex(:N)) = &0}`;;

let ORTHOGONAL_TRANSFORMATION_BETWEEN_ORTHOGONAL_SETS = `!v:num->real^N w k.
        pairwise (\i j. orthogonal (v i) (v j)) k /\
        pairwise (\i j. orthogonal (w i) (w j)) k /\
        (!i. i IN k ==> norm(v i) = norm(w i))
        ==> ?f. orthogonal_transformation f /\
                (!i. i IN k ==> f(v i) = w i)`;;

(* ------------------------------------------------------------------------- *)
(* Reflection of a vector about 0 along a line.                              *)
(* ------------------------------------------------------------------------- *)

let reflect_along = new_definition
 `reflect_along v (x:real^N) = x - (&2 * (x dot v) / (v dot v)) % v`;;

let REFLECT_ALONG_ADD = `!v x y:real^N.
      reflect_along v (x + y) = reflect_along v x + reflect_along v y`;;

let REFLECT_ALONG_MUL = `!v a x:real^N. reflect_along v (a % x) = a % reflect_along v x`;;

let LINEAR_REFLECT_ALONG = `!v:real^N. linear(reflect_along v)`;;

let REFLECT_ALONG_0 = `!v:real^N. reflect_along v (vec 0) = vec 0`;;

let REFLECT_ALONG_NEG = `!v x:real^N. reflect_along v (--x) = --(reflect_along v x)`;;

let REFLECT_ALONG_REFL = `!v:real^N. reflect_along v v = --v`;;

let REFLECT_ALONG_INVOLUTION = `!v x:real^N. reflect_along v (reflect_along v x) = x`;;

let REFLECT_ALONG_GALOIS = `!v p q:real^N. reflect_along v p = q <=> p = reflect_along v q`;;

let REFLECT_ALONG_EQ_0 = `!v x:real^N. reflect_along v x = vec 0 <=> x = vec 0`;;

let ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG = `!v:real^N. orthogonal_transformation(reflect_along v)`;;

let REFLECT_ALONG_EQ_SELF = `!v x:real^N. reflect_along v x = x <=> orthogonal v x`;;

let REFLECT_ALONG_ZERO = `reflect_along (vec 0:real^N) = I`;;

let REFLECT_ALONG_LINEAR_IMAGE = `!f:real^M->real^N v x.
        linear f /\ (!x. norm(f x) = norm x)
        ==> reflect_along (f v) (f x) = f(reflect_along v x)`;;

add_linear_invariants [REFLECT_ALONG_LINEAR_IMAGE];;

let REFLECT_ALONG_SCALE = `!c v x:real^N. ~(c = &0) ==> reflect_along (c % v) x = reflect_along v x`;;

let REFLECT_ALONG_NEGATION = `!v:real^N. reflect_along (--v) = reflect_along v`;;

let REFLECT_ALONG_1D = `!v x:real^N.
        dimindex(:N) = 1 ==> reflect_along v x = if v = vec 0 then x else --x`;;

let REFLECT_ALONG_BASIS = `!x:real^N k.
        1 <= k /\ k <= dimindex(:N)
        ==> reflect_along (basis k) x = x - (&2 * x$k) % basis k`;;

let MATRIX_REFLECT_ALONG_BASIS = `!k. 1 <= k /\ k <= dimindex(:N)
       ==> matrix(reflect_along (basis k)):real^N^N =
           lambda i j. if i = k /\ j = k then --(&1)
                       else if i = j then &1
                       else &0`;;

let ROTOINVERSION_MATRIX_REFLECT_ALONG = `!v:real^N. ~(v = vec 0) ==> rotoinversion_matrix(matrix(reflect_along v))`;;

let DET_MATRIX_REFLECT_ALONG = `!v:real^N. det(matrix(reflect_along v)) =
                if v = vec 0 then &1 else --(&1)`;;

let REFLECT_ALONG_BASIS_COMPONENT = `!x:real^N i j.
       1 <= i /\ i <= dimindex(:N) /\
       1 <= j /\ j <= dimindex(:N)
       ==> reflect_along (basis i) x$j = if j = i then --(x$j) else x$j`;;

let REFLECT_BASIS_ALONG_BASIS = `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> reflect_along (basis i:real^N) (basis j) =
             if i = j then --(basis j) else basis j`;;

let NORM_REFLECT_ALONG = `!v x:real^N. norm(reflect_along v x) = norm x`;;

let REFLECT_ALONG_EQ = `!v x y:real^N. reflect_along v x = reflect_along v y <=> x = y`;;

let REFLECT_ALONG_SURJECTIVE = `!v y:real^N. ?x. reflect_along v x = y`;;

let REFLECT_ALONG_SWITCH = `!a b:real^N.
        norm a = norm b /\ ~(a = b)
        ==> reflect_along (b - a) a = b /\ reflect_along (b - a) b = a`;;

let ROTOINVERSION_EXISTS_GEN = `!s a b:real^N.
        subspace s /\ a IN s /\ b IN s /\ ~(a = b) /\ norm a = norm b
         ==> ?f. orthogonal_transformation f /\ IMAGE f s = s /\
                 (!x. orthogonal a x /\ orthogonal b x ==> f x = x) /\
                 det (matrix f) = -- &1 /\
                 f a = b /\ f b = a`;;

let ORTHOGONAL_TRANSFORMATION_EXISTS_GEN = `!s a b:real^N.
        subspace s /\ a IN s /\ b IN s /\ norm a = norm b
         ==> ?f. orthogonal_transformation f /\ IMAGE f s = s /\
                 (!x. orthogonal a x /\ orthogonal b x ==> f x = x) /\
                 f a = b /\ f b = a`;;

(* ------------------------------------------------------------------------- *)
(* All orthogonal transformations are a composition of reflections.          *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_TRANSFORMATION_GENERATED_BY_REFLECTIONS = `!f:real^N->real^N n.
        orthogonal_transformation f /\
        dimindex(:N) <= dim {x | f x = x} + n
        ==> ?l. LENGTH l <= n /\ ALL (\v. ~(v = vec 0)) l /\
                f = ITLIST (\v h. reflect_along v o h) l I`;;

let ORTHOGONAL_TRANSFORMATION_REFLECT_INDUCT = `!P:(real^N->real^N)->bool.
        P I /\
        (!f a. orthogonal_transformation f /\ ~(a = vec 0) /\ P f
               ==> P(reflect_along a o f))
        ==> !f. orthogonal_transformation f ==> P f`;;

(* ------------------------------------------------------------------------- *)
(* Extract scaling, translation and linear invariance theorems.              *)
(* For the linear case, chain through some basic consequences automatically, *)
(* e.g. norm-preserving and linear implies injective.                        *)
(* ------------------------------------------------------------------------- *)

let SCALING_THEOREMS v =
  let th1 = UNDISCH(snd(EQ_IMP_RULE(ISPEC v NORM_POS_LT))) in
  let t = rand(concl th1) in
  end_itlist CONJ (map (C MP th1 o SPEC t) (!scaling_theorems));;

let TRANSLATION_INVARIANTS x =
  end_itlist CONJ (mapfilter (ISPEC x) (!invariant_under_translation));;

let USABLE_CONCLUSION f ths th =
  let ith = PURE_REWRITE_RULE[RIGHT_FORALL_IMP_THM] (ISPEC f th) in
  let bod = concl ith in
  let cjs = conjuncts(fst(dest_imp bod)) in
  let ths = map (fun t -> find(fun th -> aconv (concl th) t) ths) cjs in
  GEN_ALL(MP ith (end_itlist CONJ ths));;

let LINEAR_INVARIANTS =
  let sths = (CONJUNCTS o prove)
   (`(!f:real^M->real^N.
         linear f /\ (!x. norm(f x) = norm x)
         ==> (!x y. f x = f y ==> x = y)) /\
     (!f:real^N->real^N.
         linear f /\ (!x. norm(f x) = norm x) ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!x y. f x = f y ==> x = y)
                         ==> (!y. ?x. f x = y)) /\
     (!f:real^N->real^N. linear f /\ (!y. ?x. f x = y)
                         ==> (!x y. f x = f y ==> x = y))`,
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
      SIMP_TAC[GSYM LINEAR_SUB; GSYM NORM_EQ_0];
      MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE;
                ORTHOGONAL_TRANSFORMATION_INJECTIVE; ORTHOGONAL_TRANSFORMATION;
                LINEAR_SURJECTIVE_IFF_INJECTIVE]]) in
  fun f ths ->
    let ths' = ths @ mapfilter (USABLE_CONCLUSION f ths) sths in
    end_itlist CONJ
     (mapfilter (USABLE_CONCLUSION f ths') (!invariant_under_linear));;

(* ------------------------------------------------------------------------- *)
(* Tactic to pick WLOG a particular point as the origin. The conversion form *)
(* assumes it's the outermost universal variable; the tactic is more general *)
(* and allows any free or outer universally quantified variable. The list    *)
(* "avoid" is the points not to translate. There is also a tactic to help in *)
(* proving new translation theorems, which uses similar machinery.           *)
(* ------------------------------------------------------------------------- *)

let GEOM_ORIGIN_CONV,GEOM_TRANSLATE_CONV =
  let pth = `!a:real^N. a = a + vec 0 /\
                {} = IMAGE (\x. a + x) {} /\
                {} = IMAGE (IMAGE (\x. a + x)) {} /\
                (:real^N) = IMAGE (\x. a + x) (:real^N) /\
                (:real^N->bool) = IMAGE (IMAGE (\x. a + x)) (:real^N->bool) /\
                [] = MAP (\x. a + x) []`;;

(* ------------------------------------------------------------------------- *)
(* Rename existential variables in conclusion to fresh genvars.              *)
(* ------------------------------------------------------------------------- *)

let EXISTS_GENVAR_RULE =
  let rec rule vs th =
    match vs with
      [] -> th
    | v::ovs -> let x,bod = dest_exists(concl th) in
                let th1 = rule ovs (ASSUME bod) in
                let th2 = SIMPLE_CHOOSE x (SIMPLE_EXISTS x th1) in
                PROVE_HYP th (CONV_RULE (GEN_ALPHA_CONV v) th2) in
  fun th -> rule (map (genvar o type_of) (fst(strip_exists(concl th)))) th;;

(* ------------------------------------------------------------------------- *)
(* Rotate so that WLOG some point is a +ve multiple of basis vector k.       *)
(* For general N, it's better to use k = 1 so the side-condition can be      *)
(* discharged. For dimensions 1, 2 and 3 anything will work automatically.   *)
(* Could generalize by asking the user to prove theorem 1 <= k <= N.         *)
(* ------------------------------------------------------------------------- *)

let GEOM_BASIS_MULTIPLE_RULE =
  let pth = `!f. orthogonal_transformation (f:real^N->real^N)
         ==> (vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {} /\
              (:real^N) = IMAGE f (:real^N) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^N->bool) /\
              [] = MAP f []) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE (IMAGE f) s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE (IMAGE f) s))) /\
              (!P. (!g:real^1->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:real^1->real^N. P g) <=> (?g. P (f o g))) /\
              (!P. (!g:num->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:num->real^N. P g) <=> (?g. P (f o g))) /\
              (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
              (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
             ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
              (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
              (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`;;

let GEN_GEOM_NORMALIZE_TAC x avoid (asl,w as gl) =
  let avs,bod = strip_forall w
  and avs' = subtract (frees w) (freesl(map (concl o snd) asl)) in
  (MAP_EVERY X_GEN_TAC avs THEN
   MAP_EVERY (fun t -> SPEC_TAC(t,t)) (rev(subtract (avs@avs') [x])) THEN
   SPEC_TAC(x,x) THEN
   W(MATCH_MP_TAC o GEOM_NORMALIZE_RULE avoid o snd)) gl;;

let GEOM_NORMALIZE_TAC x = GEN_GEOM_NORMALIZE_TAC x [];;

(* ------------------------------------------------------------------------- *)
(* Add invariance theorems for collinearity.                                 *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_TRANSLATION_EQ = `!a s. collinear (IMAGE (\x. a + x) s) <=> collinear s`;;

add_translation_invariants [COLLINEAR_TRANSLATION_EQ];;

let COLLINEAR_TRANSLATION = `!s a. collinear s ==> collinear (IMAGE (\x. a + x) s)`;;

let COLLINEAR_LINEAR_IMAGE = `!f s. collinear s /\ linear f ==> collinear(IMAGE f s)`;;

let COLLINEAR_LINEAR_IMAGE_EQ = `!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> (collinear (IMAGE f s) <=> collinear s)`;;

add_linear_invariants [COLLINEAR_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Take a theorem "th" with outer universal quantifiers involving real^N     *)
(* and a theorem "dth" asserting |- dimindex(:M) <= dimindex(:N) and         *)
(* return a theorem replacing type :N by :M in th. Neither N or M need be a  *)
(* type variable.                                                            *)
(* ------------------------------------------------------------------------- *)

let GEOM_DROP_DIMENSION_RULE =
  let oth = prove
   (`!f:real^M->real^N.
          linear f /\ (!x. norm(f x) = norm x)
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!x. norm(f x) = norm x)`,
    MESON_TAC[PRESERVES_NORM_INJECTIVE])
  and cth = prove
   (`linear(f:real^M->real^N)
     ==> vec 0 = f(vec 0) /\
         {} = IMAGE f {} /\
         {} = IMAGE (IMAGE f) {} /\
         [] = MAP f []`,
    REWRITE_TAC[IMAGE_CLAUSES; MAP; GSYM LINEAR_0]) in
  fun dth th ->
    let ath = GEN_ALL th
    and eth = MATCH_MP ISOMETRY_UNIV_UNIV dth
    and avoid = variables(concl th) in
    let f,bod = dest_exists(concl eth) in
    let fimage = list_mk_icomb "IMAGE" [f]
    and fmap = list_mk_icomb "MAP" [f]
    and fcompose = list_mk_icomb "o" [f] in
    let fimage2 = list_mk_icomb "IMAGE" [fimage] in
    let lin,iso = CONJ_PAIR(ASSUME bod) in
    let olduniv = rand(rand(concl dth))
    and newuniv = rand(lhand(concl dth)) in
    let oldty = fst(dest_fun_ty(type_of olduniv))
    and newty = fst(dest_fun_ty(type_of newuniv)) in
    let newvar v =
       let n,t = dest_var v in
       variant avoid (mk_var(n,tysubst[newty,oldty] t)) in
    let newterm v =
      try let v' = newvar v in
          tryfind (fun f -> mk_comb(f,v')) [f;fimage;fmap;fcompose;fimage2]
      with Failure _ -> v in
    let specrule th =
      let v = fst(dest_forall(concl th)) in SPEC (newterm v) th in
    let sth = SUBS(CONJUNCTS(MATCH_MP cth lin)) ath in
    let fth = SUBS[SYM(MATCH_MP LINEAR_0 lin)] (repeat specrule sth) in
    let thps = CONJUNCTS(MATCH_MP oth (ASSUME bod)) in
    let th5 = LINEAR_INVARIANTS f thps in
    let th6 = GEN_REWRITE_RULE REDEPTH_CONV [th5] fth in
    let th7 = PROVE_HYP eth (SIMPLE_CHOOSE f th6) in
    GENL (map newvar (fst(strip_forall(concl ath)))) th7;;

(* ------------------------------------------------------------------------- *)
(* Transfer theorems automatically between same-dimension spaces.            *)
(* Given dth = A |- dimindex(:M) = dimindex(:N)                              *)
(* and a theorem th involving variables of type real^N                       *)
(* returns a corresponding theorem mapped to type real^M with assumptions A. *)
(* ------------------------------------------------------------------------- *)

let GEOM_EQUAL_DIMENSION_RULE =
  let bth = prove
   (`dimindex(:M) = dimindex(:N)
     ==> ?f:real^M->real^N.
             (linear f /\ (!y. ?x. f x = y)) /\
             (!x. norm(f x) = norm x)`,
    REWRITE_TAC[SET_RULE `(!y. ?x. f x = y) <=> IMAGE f UNIV = UNIV`] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC ISOMETRY_UNIV_SUBSPACE THEN
    REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV] THEN FIRST_ASSUM ACCEPT_TAC)
  and pth = prove
   (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
         ==> (vec 0 = f(vec 0) /\
              {} = IMAGE f {} /\
              {} = IMAGE (IMAGE f) {} /\
              (:real^N) = IMAGE f (:real^M) /\
              (:real^N->bool) = IMAGE (IMAGE f) (:real^M->bool) /\
              [] = MAP f []) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE (IMAGE f) s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE (IMAGE f) s))) /\
              (!P. (!g:real^1->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:real^1->real^N. P g) <=> (?g. P (f o g))) /\
              (!P. (!g:num->real^N. P g) <=> (!g. P (f o g))) /\
              (!P. (?g:num->real^N. P g) <=> (?g. P (f o g))) /\
              (!Q. (!l. Q l) <=> (!l. Q(MAP f l))) /\
              (!Q. (?l. Q l) <=> (?l. Q(MAP f l)))) /\
             ((!P. {x | P x} = IMAGE f {x | P(f x)}) /\
              (!Q. {s | Q s} = IMAGE (IMAGE f) {s | Q(IMAGE f s)}) /\
              (!R. {l | R l} = IMAGE (MAP f) {l | R(MAP f l)}))`,
    GEN_TAC THEN
    SIMP_TAC[SET_RULE `UNIV = IMAGE f UNIV <=> (!y. ?x. f x = y)`;
             SURJECTIVE_IMAGE] THEN
    MATCH_MP_TAC MONO_AND THEN
    REWRITE_TAC[QUANTIFY_SURJECTION_HIGHER_THM] THEN
    REWRITE_TAC[IMAGE_CLAUSES; MAP] THEN MESON_TAC[LINEAR_0]) in
  fun dth th ->
    let eth = EXISTS_GENVAR_RULE (MATCH_MP bth dth) in
    let f,bod = dest_exists(concl eth) in
    let lsth,neth = CONJ_PAIR(ASSUME bod) in
    let cth,qth = CONJ_PAIR(MATCH_MP pth lsth) in
    let th1 = CONV_RULE
     (EXPAND_QUANTS_CONV qth THENC SUBS_CONV(CONJUNCTS cth)) th in
    let ith = LINEAR_INVARIANTS f (neth::CONJUNCTS lsth) in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [BETA_THM;ith] th1 in
    let th3 = GEN f (DISCH bod th2) in
    MP (CONV_RULE (REWR_CONV LEFT_FORALL_IMP_THM) th3) eth;;
