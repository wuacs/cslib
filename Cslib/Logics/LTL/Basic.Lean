/-
Copyright (c) 2026 Dario Bekic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dario Bekic
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Logics.Modal.Semantics


@[expose] public section

namespace Cslib.Logic.Modal.LTL


inductive LTLOp where
  | next
  | until
deriving Repr, DecidableEq, BEq

def TemporalPFunctor : PFunctor where
  A := LTLOp
  B
    | .next => Unit
    | .until => Σ k, (Fin k ⊕ Unit)


def LTLModel (f: ℕ → Atom → Prop) : Modal.Model ℕ TemporalPFunctor Atom where
  v := f
  r := fun (t : LTLOp) =>
    match t with
    | .next => fun k ws => ws () = k + 1
    | .until => fun i ws => ∃K, 0 < K ∧ ∀ x, ws x =
      match x with
      | ⟨t, .inl j⟩ => if t = K then j + i else i
      | ⟨_, .inr _⟩ => i + K

scoped notation "LTL[" m "," w " ⊨ " φ "]" => Modal[m, w ⊨ φ]

open scoped Modal.Proposition InferenceSystem Satisfies Frame LTS

def next (φ : Proposition TemporalPFunctor Atom) :=
  Proposition.triangle LTLOp.next (fun _ => φ)

def until_op (ψ φ : Proposition TemporalPFunctor Atom) : Proposition TemporalPFunctor Atom :=
  φ ∨ Proposition.triangle LTLOp.until (fun k =>
    match k with
    | ⟨_, .inl _⟩ => ψ ∧ ¬φ
    | ⟨_, .inr _⟩ => φ)

def eventually (φ : Proposition TemporalPFunctor Atom) :=
  until_op (¬(.false : Proposition (τ := TemporalPFunctor) (Atom := Atom))) φ

inductive IsLTL : Proposition TemporalPFunctor Atom → Prop where
  | atom (p : Atom) : IsLTL (.atom p)
  | false : IsLTL ⊥
  | not {φ} : IsLTL φ → IsLTL (¬φ)
  | or {φ ψ} : IsLTL φ → IsLTL ψ → IsLTL (φ ∨ ψ)
  | next {φ} : IsLTL φ → IsLTL (next φ)
  | until {φ ψ} : IsLTL φ → IsLTL ψ → IsLTL (until_op φ ψ)

@[scoped grind =, modal =]
theorem Satisfies.ltl_atom_iff {p : Atom} : ⇓LTL[m, s ⊨ p] ↔ m.v s p := by rfl

theorem Satisfies.ltl_next_iff {f : ℕ → Atom → Prop}:
  ⇓LTL[LTLModel f, i ⊨ next φ] ↔ ⇓LTL[LTLModel f, i+1 ⊨ φ] := by
  apply Iff.intro
  · intro h
    rw [← derivation_def] at h
    rw [← derivation_def]
    rw [next] at h
    have ⟨wit, l⟩ := h
    simp at l
    have hpr := l.right ()
    have hpt : wit () = i + 1 := by
      have hpl := l.left
      exact l.left
    rw [hpt] at hpr
    exact hpr
  · intro h
    rw [← derivation_def] at h
    rw [← derivation_def]
    rw [next]
    use fun _ => i + 1
    simp only [TemporalPFunctor, LTLModel, forall_const, true_and]
    exact h


theorem Satisfies.ltl_until_iff {f : ℕ → Atom → Prop}:
  ⇓LTL[LTLModel f, i ⊨ until_op φ ψ] ↔
  ∃x, ⇓LTL[LTLModel f, i + x ⊨ ψ] ∧ ∀y, y < x → ⇓LTL[LTLModel f, i + y ⊨ (φ ∧ ¬ψ)] := by
  constructor
  · intro h
    rw [until_op, Satisfies.or_iff_or] at h
    cases h with
    | inl hA =>
      use 0
      grind
    | inr hB =>
      have ⟨hS, hW⟩ := hB
      simp at hW
      have hp := hW.left
      simp only [LTLModel] at hp
      have ⟨K, hp⟩ := hp
      use K
      constructor
      · have hp1 := hW.right ⟨K, .inr ()⟩
        simp only at hp1
        rw [hp.right ⟨K, .inr ()⟩] at hp1
        simp only at hp1
        exact hp1
      · intro y hy
        have hp2 := hW.right ⟨K, .inl (Fin.mk y hy)⟩
        simp only at hp2
        rw [hp.right ⟨K, .inl (Fin.mk y hy)⟩] at hp2
        simp only [↓reduceIte] at hp2
        rw [Nat.add_comm]
        exact hp2
  · intro h
    have ⟨w, hp⟩ := h
    let f : TemporalPFunctor.B LTLOp.until → ℕ :=
      fun k => match k with
      | ⟨k, .inl t⟩ => if k = w then t + i else i
      | ⟨_, .inr ()⟩ => i + w
    rw [until_op, Satisfies.or_iff_or]
    by_cases hp1 : w > 0
    · apply Or.inr
      use f
      simp only
      constructor
      · rw [LTLModel]
        simp only
        use w
        constructor
        · use hp1
        · intro x
          rcases x with ⟨k, t | ⟨⟩⟩
          · simp only [f]
          · simp only [f]
      · intro i
        rcases i with ⟨k, t | ⟨⟩⟩
        · simp [f]
          by_cases hp2 : k = w
          · grind
          · grind
        · simp only [f]
          exact hp.left
    · apply Or.inl
      have hp2 : w = 0 := by grind
      have hp3 := hp.left
      rw [hp2] at hp3
      use hp3

theorem Satisfies.ltl_eventually_iff {f : ℕ → Atom → Prop}:
  ⇓LTL[LTLModel f, i ⊨ eventually φ] ↔ ∃x, ⇓LTL[LTLModel f, i + x ⊨ φ] := by
  classical
  rw [eventually, Satisfies.ltl_until_iff]
  apply Iff.intro
  · intro h
    have ⟨w, h⟩ := h
    use w
    exact h.left
  · intro h
    set K := Nat.find h with hK
    have hKp := Nat.find_spec h
    use K
    constructor
    · exact hKp
    · intro y hy
      rw [Satisfies.and_iff_and]
      constructor
      · grind
      · have hmin : ∀ m < K, (¬ ⇓LTL[LTLModel f, i + m ⊨ φ]) := fun m hm => Nat.find_min h hm
        exact hmin y hy

theorem Satisfies.ltl_expansion_law {f : ℕ → Atom → Prop}:
  ⇓LTL[LTLModel f, i ⊨ until_op ψ φ] ↔
  ⇓LTL[LTLModel f, i ⊨ φ ∨ ((ψ ∧ ¬ φ) ∧ (next (until_op ψ φ)))]
  := by
  apply Iff.intro
  · intro h
    rw [Satisfies.or_iff_or]
    rw [Satisfies.ltl_until_iff] at h
    obtain ⟨w, hw⟩ := h
    by_cases hp : w = 0
    · rw [hp] at hw
      grind
    · apply Or.inr
      rw [Satisfies.and_iff_and]
      constructor
      · exact hw.right 0 (by grind)
      · rw [Satisfies.ltl_next_iff, Satisfies.ltl_until_iff]
        use w - 1
        constructor
        · rw [← Nat.add_sub_assoc (by grind) (i + 1)]
          simp only [Nat.succ_add_sub_one]
          exact hw.left
        · intro y hy
          have h := hw.right (y + 1) (by omega)
          rw [show i + (y + 1) = i + 1 + y by omega] at h
          exact h
  · intro a
    cases a with
    | inl hpl =>
      simp at hpl
      rw [Satisfies.ltl_until_iff]
      use 0
      grind
    | inr hpr =>
      simp only at hpr
      rw [Satisfies.ltl_until_iff]
      obtain ⟨hψ, hnext⟩ := (Satisfies.and_iff_and (m := LTLModel f)).mp hpr
      rw [Satisfies.ltl_next_iff, Satisfies.ltl_until_iff] at hnext
      obtain ⟨x, hx⟩ := hnext
      use x + 1
      constructor
      · grind
      · intro y hy
        by_cases hp : y = 0
        · rw [hp]
          grind
        · have hp3 := hx.right (y-  1) (by grind)
          rw [Nat.add_comm i 1, ← Nat.add_sub_assoc (by grind) (1 + i)] at hp3
          grind


end Cslib.Logic.Modal.LTL
