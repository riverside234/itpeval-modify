Class LatticeLike (A : Type) := {
  le   : A -> A -> Prop;
  inf  : A -> A -> A;
  sup  : A -> A -> A;

  le_refl  : forall x, le x x;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_antisym : forall x y, le x y -> le y x -> x = y;

  le_inf_left  : forall a b, le (inf a b) a;
  le_inf_right : forall a b, le (inf a b) b;
  le_inf_intro : forall c a b, le c a -> le c b -> le c (inf a b);

  le_sup_left  : forall a b, le a (sup a b);
  le_sup_right : forall a b, le b (sup a b);
  sup_le_intro : forall a b c, le a c -> le b c -> le (sup a b) c
}.

Section LatticeFacts.
  Context {A : Type} {L : LatticeLike A}.

  Infix "≤" := le (at level 70, no associativity).

  Notation "x ⊓ y" := (inf x y) (at level 40).
  Notation "x ⊔ y" := (sup x y) (at level 50).

  Lemma inf_comm (a b : A) : a ⊓ b = b ⊓ a.
  Proof.
    apply le_antisym.
    - pose proof (le_inf_right a b) as H1.
      pose proof (le_inf_left a b)  as H2.
      pose proof (le_inf_intro (a ⊓ b) b a H1 H2) as H3.
      exact H3.
    - pose proof (le_inf_right b a) as H1.
      pose proof (le_inf_left b a)  as H2.
      pose proof (le_inf_intro (b ⊓ a) a b H1 H2) as H3.
      exact H3.
  Qed.

  Lemma sup_comm (a b : A) : a ⊔ b = b ⊔ a.
  Proof.
    apply le_antisym.
    - pose proof (le_sup_right b a) as Ha.
      pose proof (le_sup_left  b a) as Hb.
      pose proof (sup_le_intro a b (b ⊔ a) Ha Hb) as H3.
      exact H3.
    - pose proof (le_sup_right a b) as Hb.
      pose proof (le_sup_left  a b) as Ha.
      pose proof (sup_le_intro b a (a ⊔ b) Hb Ha) as H3.
      exact H3.
  Qed.

  Lemma inf_assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
  Proof.
    apply le_antisym.
    - pose proof (le_inf_left (a ⊓ b) c) as Hab_le.
      pose proof (le_inf_left a b) as Ha_le.
      pose proof (le_trans _ _ _ Hab_le Ha_le) as H_to_a.
      pose proof (le_inf_right (a ⊓ b) c) as H_to_c.
      pose proof (le_inf_right a b) as Hab_to_b.
      pose proof (le_trans _ _ _ Hab_le Hab_to_b) as H_to_b.
      pose proof (le_inf_intro ((a ⊓ b) ⊓ c) a (b ⊓ c) H_to_a (le_inf_intro _ _ _ H_to_b H_to_c)) as H.
      exact H.
    - pose proof (le_inf_left a (b ⊓ c)) as H_to_a.
      pose proof (le_inf_right a (b ⊓ c)) as Habc.
      pose proof (le_inf_left b c) as H_to_b.
      pose proof (le_trans _ _ _ Habc H_to_b) as H_b.
      pose proof (le_inf_right b c) as H_to_c.
      pose proof (le_trans _ _ _ Habc H_to_c) as H_c.
      pose proof (le_inf_left (a ⊓ b) c) as Habc_left.
      pose proof (le_inf_intro (a ⊓ (b ⊓ c)) (a ⊓ b) c (le_inf_intro _ _ _ H_to_a H_b) H_c) as H.
      exact H.
  Qed.

  Lemma sup_assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
  Proof.
    apply le_antisym.
    - pose proof (le_sup_left a (b ⊔ c)) as Ha_to.
      pose proof (le_sup_left b c) as Hb_to_bc.
      pose proof (le_trans _ _ _ Hb_to_bc (le_sup_right a (b ⊔ c))) as Hb_to.
      pose proof (sup_le_intro a b (a ⊔ (b ⊔ c)) Ha_to Hb_to) as Hab_to.
      pose proof (le_sup_right b c) as Hc_to_bc.
      pose proof (le_trans _ _ _ Hc_to_bc (le_sup_right a (b ⊔ c))) as Hc_to.
      pose proof (sup_le_intro (a ⊔ b) c (a ⊔ (b ⊔ c)) Hab_to Hc_to) as H.
      exact H.
    - pose proof (le_sup_left a b) as Ha_ab.
      pose proof (le_sup_left (a ⊔ b) c) as Hab_to.
      pose proof (le_trans _ _ _ Ha_ab Hab_to) as Ha_to.
      pose proof (le_sup_right a b) as Hb_to_ab.
      pose proof (le_sup_right (a ⊔ b) c) as Hc_to.
      pose proof (le_trans _ _ _ Hb_to_ab Hab_to) as Hb_to.
      pose proof (sup_le_intro b c ((a ⊔ b) ⊔ c) Hb_to Hc_to) as Hbc_to.
      pose proof (sup_le_intro a (b ⊔ c) ((a ⊔ b) ⊔ c) Ha_to Hbc_to) as H.
      exact H.
  Qed.

  Lemma inf_absorption (a b : A) : a ⊓ (a ⊔ b) = a.
  Proof.
    apply le_antisym.
    - apply le_inf_left.
    - pose proof (le_refl a) as Ha.
      pose proof (le_sup_left a b) as Hab.
      pose proof (le_inf_intro a a (a ⊔ b) Ha Hab) as H.
      exact H.
  Qed.

  Lemma sup_absorption (a b : A) : a ⊔ (a ⊓ b) = a.
  Proof.
    apply le_antisym.
    - pose proof (le_refl a) as Ha.
      pose proof (le_inf_left a b) as Hab.
      pose proof (sup_le_intro a (a ⊓ b) a Ha Hab) as H.
      exact H.
    - apply le_sup_left.
  Qed.

End LatticeFacts.
