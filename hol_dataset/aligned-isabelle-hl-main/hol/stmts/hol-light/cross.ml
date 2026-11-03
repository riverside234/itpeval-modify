(* ========================================================================= *)
(* Cross products in real^3.                                                 *)
(* ========================================================================= *)

needs "Multivariate/topology.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* The definition.                                                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cross",(20,"right"));;

let cross = new_definition
 `(a:real^3) cross (b:real^3) =
    vector [a$2 * b$3 - a$3 * b$2;
            a$3 * b$1 - a$1 * b$3;
            a$1 * b$2 - a$2 * b$1] :real^3`;;

(* ------------------------------------------------------------------------- *)
(* Some simple automation.                                                   *)
(* ------------------------------------------------------------------------- *)

let VEC3_TAC =
  SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_3; SUM_3; DIMINDEX_3; VECTOR_3;
           vector_add; vec; dot; cross; orthogonal; basis; DET_3;
           vector_neg; vector_sub; vector_mul; ARITH] THEN
  CONV_TAC REAL_RING;;

let VEC3_RULE tm = prove(tm,VEC3_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas.                                                             *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_CROSS = `!x y. orthogonal (x cross y) x /\ orthogonal (x cross y) y /\
         orthogonal x (x cross y) /\ orthogonal y (x cross y)`;;

let CROSS_LZERO = `!x. (vec 0) cross x = vec 0`;;

let CROSS_RZERO = `!x. x cross (vec 0) = vec 0`;;

let CROSS_SKEW = `!x y. (x cross y) = --(y cross x)`;;

let CROSS_REFL = `!x. x cross x = vec 0`;;

let CROSS_LADD = `!x y z. (x + y) cross z = (x cross z) + (y cross z)`;;

let CROSS_RADD = `!x y z. x cross (y + z) = (x cross y) + (x cross z)`;;

let CROSS_LMUL = `!c x y. (c % x) cross y = c % (x cross y)`;;

let CROSS_RMUL = `!c x y. x cross (c % y) = c % (x cross y)`;;

let CROSS_LNEG = `!x y. (--x) cross y = --(x cross y)`;;

let CROSS_RNEG = `!x y. x cross (--y) = --(x cross y)`;;

let CROSS_LSUB = `!x y z. (x - y) cross z = x cross z - y cross z`;;

let CROSS_RSUB = `!x y z. x cross (y - z) = x cross y - x cross z`;;

let CROSS_JACOBI = `!x y z.
    x cross (y cross z) + y cross (z cross x) + z cross (x cross y) = vec 0`;;

let CROSS_LAGRANGE = `!x y z. x cross (y cross z) = (x dot z) % y - (x dot y) % z`;;

let CROSS_TRIPLE = `!x y z.  (x cross y) dot z = (y cross z) dot x`;;

let DOT_CROSS_SELF = `(!x y. x dot (x cross y) = &0) /\
   (!x y. x dot (y cross x) = &0) /\
   (!x y. (x cross y) dot y = &0) /\
   (!x y. (y cross x) dot y = &0)`;;

let CROSS_COMPONENTS = `!x y. (x cross y)$1 = x$2 * y$3 - y$2 * x$3 /\
         (x cross y)$2 = x$3 * y$1 - y$3 * x$1 /\
         (x cross y)$3 = x$1 * y$2 - y$1 * x$2`;;

let CROSS_BASIS = `(basis 1) cross (basis 2) = basis 3 /\
   (basis 2) cross (basis 1) = --(basis 3) /\
   (basis 2) cross (basis 3) = basis 1 /\
   (basis 3) cross (basis 2) = --(basis 1) /\
   (basis 3) cross (basis 1) = basis 2 /\
   (basis 1) cross (basis 3) = --(basis 2)`;;

let CROSS_BASIS_NONZERO = `!u. ~(u = vec 0)
       ==> ~(u cross basis 1 = vec 0) \/
           ~(u cross basis 2 = vec 0) \/
           ~(u cross basis 3 = vec 0)`;;

let CROSS_DOT_CANCEL = `!x y z.
     x dot y = x dot z /\ x cross y = x cross z /\ ~(x = vec 0) ==> y = z`;;

let NORM_CROSS_DOT = `!x y. norm(x cross y) pow 2 + (x dot y) pow 2 = (norm(x) * norm y) pow 2`;;

let DOT_CROSS_DET = `!x y z. x dot (y cross z) = det(vector[x;y;z]:real^3^3)`;;

let CROSS_CROSS_DET = `!w x y z. (w cross x) cross (y cross z) =
                det(vector[w;x;z]:real^3^3) % y -
                det(vector[w;x;y]:real^3^3) % z`;;

let DOT_CROSS = `!w x y z. (w cross x) dot (y cross z) =
                (w dot y) * (x dot z) - (w dot z) * (x dot y)`;;

let NORM_CROSS = `!x y. norm(x cross y) pow 2 =
           norm(x) pow 2 * norm(y) pow 2 - (x dot y) pow 2`;;

let CROSS_EQ_0 = `!x y. x cross y = vec 0 <=> collinear{vec 0,x,y}`;;

let CROSS_0 = `(!x. vec 0 cross x = vec 0) /\
   (!x. x cross vec 0 = vec 0)`;;

let CROSS_EQ_SELF = `(!x y. x cross y = x <=> x = vec 0) /\
   (!x y. x cross y = y <=> y = vec 0)`;;

let NORM_AND_CROSS_EQ_0 = `!x y. x dot y = &0 /\ x cross y = vec 0 <=> x = vec 0 \/ y = vec 0`;;

let BILINEAR_CROSS = `bilinear(cross)`;;

(* ------------------------------------------------------------------------- *)
(* Preservation by rotation, or other orthogonal transformation up to sign.  *)
(* ------------------------------------------------------------------------- *)

let CROSS_MATRIX_MUL = `!A x y. transp A ** ((A ** x) cross (A ** y)) = det A % (x cross y)`;;

let CROSS_ORTHOGONAL_MATRIX = `!A x y. orthogonal_matrix A
           ==> (A ** x) cross (A ** y) = det A % (A ** (x cross y))`;;

let CROSS_ROTATION_MATRIX = `!A x y. rotation_matrix A
           ==> (A ** x) cross (A ** y) =  A ** (x cross y)`;;

let CROSS_ROTOINVERSION_MATRIX = `!A x y. rotoinversion_matrix A
           ==> (A ** x) cross (A ** y) =  --(A ** (x cross y))`;;

let CROSS_ORTHOGONAL_TRANSFORMATION = `!f x y.
        orthogonal_transformation f
        ==> (f x) cross (f y) = det(matrix f) % f(x cross y)`;;

let CROSS_LINEAR_IMAGE = `!f x y. linear f /\ (!x. norm(f x) = norm x) /\ det(matrix f) = &1
           ==> (f x) cross (f y) = f(x cross y)`;;

(* ------------------------------------------------------------------------- *)
(* Continuity.                                                               *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CROSS = `!net:(A)net f g.
        f continuous net /\ g continuous net
        ==> (\x. (f x) cross (g x)) continuous net`;;

let CONTINUOUS_ON_CROSS = `!f:real^N->real^3 g s.
        f continuous_on s /\ g continuous_on s
        ==> (\x. (f x) cross (g x)) continuous_on s`;;

(* ------------------------------------------------------------------------- *)
(* Prove a weaker variant for more convenient interface with functions       *)
(* intended to work in 1 dimension.                                          *)
(* ------------------------------------------------------------------------- *)

let CROSS_LINEAR_IMAGE_WEAK = `!f x y. linear f /\ (!x. norm(f x) = norm x) /\
           (2 <= dimindex(:3) ==> det(matrix f) = &1)
           ==> (f x) cross (f y) = f(x cross y)`;;

add_linear_invariants [CROSS_LINEAR_IMAGE_WEAK];;
