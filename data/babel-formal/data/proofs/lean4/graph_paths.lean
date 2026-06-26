universe u

namespace GraphPath

variable {V : Type u}

def Edge (V : Type u) := V → V → Prop

inductive Path (E : Edge V) : V → V → Prop
| nil  : ∀ v, Path E v v
| step : ∀ {u v w}, Path E u v → E v w → Path E u w


variable {E : Edge V}

theorem refl (v : V) : Path (E:=E) v v := Path.nil v

theorem trans {u v w : V} : Path (E:=E) u v → Path (E:=E) v w → Path (E:=E) u w :=
by
  intro p1 p2; induction p2 with
  | nil => simpa using p1
  | step p2' evw ih => exact Path.step ih evw

def Erev (E : Edge V) : Edge V := fun x y => E y x

def undirected (E : Edge V) : Prop := ∀ x y, E x y → E y x

theorem reverse_path {u v : V} (hE : undirected E) :
  Path (E:=E) u v → Path (E:=E) v u :=
by
  intro p; induction p with
  | nil => exact Path.nil _
  | step p' evw ih =>
      have hwv : Path (E:=E) _ _ := Path.step (E:=E) (Path.nil _) (hE _ _ evw)
      exact trans (E:=E) hwv ih

theorem concat_edge_right {u v w : V} :
  Path (E:=E) u v → E v w → Path (E:=E) u w := by
  intro p evw; exact Path.step p evw

theorem concat {u v w : V} :
  Path (E:=E) u v → Path (E:=E) v w → Path (E:=E) u w := by
  intro p q; exact trans p q

theorem edge_path {u v : V} : E u v → Path (E:=E) u v := by
 intro euv; exact Path.step (Path.nil u) euv

theorem concat_edge_left {u v w : V} :
  E u v → Path (E:=E) v w → Path (E:=E) u w := by
 intro euv pvw; exact trans (edge_path (E:=E) euv) pvw

theorem concat3 {u v w t : V} :
  Path (E:=E) u v → Path (E:=E) v w → Path (E:=E) w t → Path (E:=E) u t := by
  intro puv pvw pwt; exact trans (trans puv pvw) pwt

theorem reverse_in_Erev {u v : V} :
  Path (E:=E) u v → Path (E:=Erev E) v u := by
  intro p; induction p with
  | nil => exact Path.nil _
  | step p' evw ih =>
      have hwv : Path (E:=Erev E) _ _ := Path.step (Path.nil _) evw
      exact trans hwv ih

theorem cycle_refl {v w : V} :
  Path (E:=E) v w → Path (E:=E) w v → Path (E:=E) v v := by
  intro pvw pwv; exact trans pvw pwv

end GraphPath
