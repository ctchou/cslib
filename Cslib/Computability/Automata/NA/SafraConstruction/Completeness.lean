/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.SafraSpec
public import Mathlib.Data.Set.Finite.List

/-! # Completeness of the Safra construction

-/

@[expose] public section

namespace Cslib.SafraConstruction

open Descriptive Set Filter Automata ωAcceptor

variable {State Symbol : Type*}
  {na : NA.Buchi State Symbol} {mda : DA.Rabin (MacroState State) Symbol}
  {as : ωSequence Symbol} {ss : ωSequence State}

theorem macro_run_wellFormed (hs : SafraSpec na mda) (as : ωSequence Symbol) (n : ℕ) :
    (mda.run as n).WellFormed := by
  induction n with
  | zero => exact hs.start_wf
  | succ n ih => rw [DA.run_succ]; exact hs.wf_inv _ _ ih

theorem state_mem_macro_states (hs : SafraSpec na mda) (hr : na.Run as ss) (n : ℕ) :
    ss n ∈ ((mda.run as) n).states := by
  induction n with
  | zero => simpa [hs.start_states] using hr.start
  | succ n ih =>
    rw [DA.run_succ, hs.states_image]
    exact Set.mem_biUnion ih (hr.trans n)

def host (hs : SafraSpec na mda) (hr : na.Run as ss) (k : ℕ) : List ℕ :=
  (mda.run as k).host ⟨ss k, state_mem_macro_states hs hr k⟩

def freqHosts (hs : SafraSpec na mda) (hr : na.Run as ss) : Set (List ℕ) :=
  {x | ∃ᶠ k in atTop, host hs hr k = x}

/-- A set of lists of bounded length with bounded entries is finite. -/
lemma finite_bounded_lists (n : ℕ) :
    {x : List ℕ | x.length ≤ n ∧ ∀ i ∈ x, i < n}.Finite := by
  refine ((List.finite_length_le (Fin n) n).image (List.map Fin.val)).subset ?_
  rintro x ⟨hlen, hlt⟩
  exact ⟨x.pmap Fin.mk hlt, by simpa using hlen, by simp [List.map_pmap]⟩

/-- Every host lies in a fixed finite set of lists. -/
theorem host_mem_bounded [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) (k : ℕ) :
    host hs hr k ∈ {x : List ℕ | x.length ≤ Nat.card State ∧ ∀ i ∈ x, i < Nat.card State} :=
  have hwf := macro_run_wellFormed hs as k
  have hx := (mda.run as k).host_mem_safraTree ⟨ss k, state_mem_macro_states hs hr k⟩
  ⟨((mda.run as k).length_lt_of_mem_safraTree hwf hx).le,
    fun _ hi => (mda.run as k).lt_of_mem_safraTree hwf hx hi⟩

/-- Eventually, every host is one that occurs infinitely often. -/
theorem eventually_mem_freqHosts [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) :
    ∀ᶠ k in atTop, host hs hr k ∈ freqHosts hs hr := by
  set S := {x : List ℕ | x.length ≤ Nat.card State ∧ ∀ i ∈ x, i < Nat.card State}
  have hall : ∀ x ∈ S \ freqHosts hs hr, ∀ᶠ k in atTop, host hs hr k ≠ x :=
    fun x hx => by simpa [freqHosts, Filter.not_frequently] using hx.2
  filter_upwards [((finite_bounded_lists _).sdiff).eventually_all.2 hall] with k hk
  by_contra hn
  exact hk (host hs hr k) ⟨host_mem_bounded hs hr k, hn⟩ rfl

theorem freqHosts_nonempty [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) :
    (freqHosts hs hr).Nonempty := by
  set N := Nat.card State
  have hfS := host_mem_bounded hs hr
  by_contra hne
  have hall : ∀ x ∈ {x : List ℕ | x.length ≤ N ∧ ∀ i ∈ x, i < N}, ∀ᶠ k in atTop, host hs hr k ≠ x :=
    fun x _ => by
      have : x ∉ freqHosts hs hr := fun hx => hne ⟨x, hx⟩
      simpa [freqHosts, Filter.not_frequently, host] using this
  obtain ⟨k, hk⟩ := ((finite_bounded_lists N).eventually_all.2 hall).exists
  exact hk (host hs hr k) (hfS k) rfl

open Classical in
/-- The minimal length of the hosts that occur infinitely often along the run `ss`
(the `l` in the "only if" part of the proof of Proposition 1 of Schewe's paper). -/
noncomputable def shortestHostLen [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ :=
  Nat.find (p := fun n => ∃ x ∈ freqHosts hs hr, x.length = n) <| by
    obtain ⟨x, hx⟩ := freqHosts_nonempty hs hr
    exact ⟨x.length, x, hx, rfl⟩

theorem shortestHostLen_infinitely [Finite State]
    (hs : SafraSpec na mda) (hr : na.Run as ss) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ k, (host hs hr (f 0 + k)).length ≥ shortestHostLen hs hr) ∧
      (∀ i, (host hs hr (f i)).length = shortestHostLen hs hr) := by
  classical
  obtain ⟨x, hx, hlen⟩ := Nat.find_spec (p := fun n => ∃ x ∈ freqHosts hs hr, x.length = n) <| by
    obtain ⟨x, hx⟩ := freqHosts_nonempty hs hr
    exact ⟨x.length, x, hx, rfl⟩
  obtain ⟨n, hn⟩ := eventually_atTop.1 (eventually_mem_freqHosts hs hr)
  have hfreq : ∃ᶠ k in atTop, host hs hr k = x ∧ n ≤ k :=
    Frequently.and_eventually hx (eventually_ge_atTop n)
  obtain ⟨f, hmono, hf⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨f, hmono, fun k => Nat.find_min' _ ⟨_, hn _ ?_, rfl⟩, fun i => ?_⟩
  · exact (hf 0).2.trans (Nat.le_add_right _ k)
  · rw [(hf i).1]
    exact hlen

noncomputable def shortestHostPos [Finite State]
    (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ → ℕ :=
  Classical.choose (shortestHostLen_infinitely hs hr)

theorem shortestHostPos_spec [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) :
    StrictMono (shortestHostPos hs hr) ∧
      (∀ k, (host hs hr (shortestHostPos hs hr 0 + k)).length ≥ shortestHostLen hs hr) ∧
      (∀ i, (host hs hr (shortestHostPos hs hr i)).length = shortestHostLen hs hr) :=
  Classical.choose_spec (shortestHostLen_infinitely hs hr)

noncomputable def shortestHostVal [Finite State]
    (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ → List ℕ :=
  host hs hr ∘ shortestHostPos hs hr

/-- In one step, the length-`l` prefix of the host does not increase lexicographically,
provided both hosts have length at least `l`. -/
theorem host_take_succ_le (hs : SafraSpec na mda) (hr : na.Run as ss) {l t : ℕ}
    (hl : l ≤ (host hs hr t).length) (hl' : l ≤ (host hs hr (t + 1)).length) :
    (host hs hr (t + 1)).take l ≤ (host hs hr t).take l := by
  obtain ⟨h1, -⟩ := hs.forward (mda.run as t) (as t) (ss t) (ss (t + 1))
    (state_mem_macro_states hs hr t) (state_mem_macro_states hs hr (t + 1)) (hr.trans t)
  rcases h1 with ⟨hdl, -⟩ | ⟨hp, -⟩
  · exact take_le_take_of_deepLeft hl hdl
  · exact (take_eq_of_prefix hp hl').symm.le

theorem shortestHostVal_antitone [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) :
    Antitone (shortestHostVal hs hr) := by
  have hspec : StrictMono (shortestHostPos hs hr) ∧
      (∀ k, (host hs hr (shortestHostPos hs hr 0 + k)).length ≥ shortestHostLen hs hr) ∧
      (∀ i, (host hs hr (shortestHostPos hs hr i)).length = shortestHostLen hs hr) :=
    Classical.choose_spec (shortestHostLen_infinitely hs hr)
  obtain ⟨hmono, hge, heq⟩ := hspec
  set f := shortestHostPos hs hr
  set l := shortestHostLen hs hr
  let g : ℕ → List ℕ := fun k => (host hs hr (f 0 + k)).take l
  have hg : Antitone g := antitone_nat_of_succ_le fun k =>
    host_take_succ_le hs hr (hge k) (hge (k + 1))
  have key : ∀ i, shortestHostVal hs hr i = g (f i - f 0) := fun i => by
    simp only [shortestHostVal, g, Function.comp_apply,
      Nat.add_sub_cancel' (hmono.monotone (Nat.zero_le i))]
    exact (List.take_of_length_le (heq i).le).symm
  intro i j hij
  rw [key, key]
  exact hg (Nat.sub_le_sub_right (hmono.monotone hij) _)

theorem shortestHostVal_eventually_stable [Finite State]
    (hs : SafraSpec na mda) (hr : na.Run as ss) :
    ∃ n x, ∀ k, shortestHostVal hs hr (n + k) = x := by
  have hfin : (range (shortestHostVal hs hr)).Finite :=
    (finite_bounded_lists (Nat.card State)).subset <| by
      rintro _ ⟨i, rfl⟩
      exact host_mem_bounded hs hr _
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ :=
    exists_min_image (range (shortestHostVal hs hr)) id hfin (range_nonempty _)
  refine ⟨n, shortestHostVal hs hr n, fun k => ?_⟩
  exact le_antisymm (shortestHostVal_antitone hs hr (Nat.le_add_right n k)) (hmin _ ⟨n + k, rfl⟩)

noncomputable def shortestHostStart [Finite State]
    (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ :=
  Classical.choose (shortestHostVal_eventually_stable hs hr)

noncomputable def stableHost [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) : List ℕ :=
  shortestHostVal hs hr (shortestHostStart hs hr)

theorem stableHost_spec [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) (k : ℕ) :
    shortestHostVal hs hr (shortestHostStart hs hr + k) = stableHost hs hr := by
  obtain ⟨x, hx⟩ := Classical.choose_spec (shortestHostVal_eventually_stable hs hr)
  have h0 := hx 0
  simp only [Nat.add_zero] at h0
  rw [stableHost, ← shortestHostStart] at *
  rw [hx k, h0]

theorem host_shortestHostPos [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    {j : ℕ} (hj : shortestHostStart hs hr ≤ j) :
    host hs hr (shortestHostPos hs hr j) = stableHost hs hr := by
  have := stableHost_spec hs hr (j - shortestHostStart hs hr)
  rwa [Nat.add_sub_cancel' hj] at this

theorem shortestHostLen_le_length [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    {t : ℕ} (ht : shortestHostPos hs hr 0 ≤ t) :
    shortestHostLen hs hr ≤ (host hs hr t).length := by
  have := (shortestHostPos_spec hs hr).2.1 (t - shortestHostPos hs hr 0)
  rwa [Nat.add_sub_cancel' ht] at this

/-- From `shortestHostPos 0` on, the length-`l` prefix of the host is lexicographically
antitone in time. -/
theorem host_take_antitone [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    {t t' : ℕ} (ht : shortestHostPos hs hr 0 ≤ t) (htt : t ≤ t') :
    (host hs hr t').take (shortestHostLen hs hr) ≤ (host hs hr t).take (shortestHostLen hs hr) := by
  induction t', htt using Nat.le_induction with
  | base => exact le_rfl
  | succ t' htt ih =>
    exact (host_take_succ_le hs hr (shortestHostLen_le_length hs hr (ht.trans htt))
      (shortestHostLen_le_length hs hr (ht.trans (htt.trans (Nat.le_succ _))))).trans ih

/-- Eventually, the length-`l` prefix of every host is `stableHost`. -/
theorem host_take_eq_stableHost [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    {t : ℕ} (ht : shortestHostPos hs hr (shortestHostStart hs hr) ≤ t) :
    (host hs hr t).take (shortestHostLen hs hr) = stableHost hs hr := by
  obtain ⟨hmono, -, heq⟩ := shortestHostPos_spec hs hr
  set f := shortestHostPos hs hr
  set n0 := shortestHostStart hs hr
  have htake : ∀ k, (host hs hr (f (n0 + k))).take (shortestHostLen hs hr) = stableHost hs hr :=
    fun k => by
      rw [List.take_of_length_le (heq _).le]
      exact stableHost_spec hs hr k
  have hf0 : f 0 ≤ f n0 := hmono.monotone (Nat.zero_le _)
  apply le_antisymm
  · have h := host_take_antitone hs hr hf0 ht
    rwa [← Nat.add_zero n0, htake 0] at h
  · have hle : t ≤ f (n0 + t) := (Nat.le_add_left t n0).trans (hmono.id_le _)
    have h := host_take_antitone hs hr (hf0.trans ht) hle
    rwa [htake t] at h

theorem stableHost_prefix [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    {t : ℕ} (ht : shortestHostPos hs hr (shortestHostStart hs hr) ≤ t) :
    stableHost hs hr <+: host hs hr t := by
  rw [← host_take_eq_stableHost hs hr ht]
  exact List.take_prefix _ _

noncomputable def stableHostStart [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) : ℕ :=
  shortestHostPos hs hr (shortestHostStart hs hr) + 1

/-- `stableHost` is eventually always in the stable tree. -/
theorem stableHost_stable [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss) (k : ℕ) :
    stableHost hs hr ∈ (mda.run as (stableHostStart hs hr + k)).stableTree := by
  set T := shortestHostPos hs hr (shortestHostStart hs hr)
  rw [stableHostStart]
  have ht : T ≤ T + k := Nat.le_add_right T k
  obtain ⟨-, h2⟩ := hs.forward (mda.run as (T + k)) (as (T + k)) (ss (T + k)) (ss (T + k + 1))
    (state_mem_macro_states hs hr (T + k)) (state_mem_macro_states hs hr (T + k + 1))
    (hr.trans _)
  rw [Nat.add_right_comm]
  exact h2 _ (stableHost_prefix hs hr ht) (stableHost_prefix hs hr (ht.trans (Nat.le_succ _)))

/-- If `stableHost` is not accepting at time `t + 1`, then the host can only be `stableHost`
at time `t + 1` if it already was at time `t`. -/
theorem host_eq_stableHost_of_succ [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    {t : ℕ} (ht : shortestHostPos hs hr (shortestHostStart hs hr) ≤ t)
    (hna : ¬ stableHost hs hr ∈ (mda.run as (t + 1)).accept)
    (h : host hs hr (t + 1) = stableHost hs hr) : host hs hr t = stableHost hs hr := by
  obtain ⟨h1, -⟩ := hs.forward (mda.run as t) (as t) (ss t) (ss (t + 1))
    (state_mem_macro_states hs hr t) (state_mem_macro_states hs hr (t + 1)) (hr.trans t)
  have hp := stableHost_prefix hs hr ht
  rcases h1 with ⟨hdl, -⟩ | ⟨-, ha⟩
  · change DeepLeft (host hs hr (t + 1)) (host hs hr t) at hdl
    rw [h] at hdl
    rcases hdl with hp' | ⟨-, hnp⟩
    · exact (hp.eq_of_length_le hp'.length_le).symm
    · exact absurd hp hnp
  · change host hs hr (t + 1) ∈ (mda.run as (t + 1)).accept at ha
    rw [h] at ha
    exact absurd ha hna

/-- If `stableHost` is eventually never accepting, then the host is eventually
always `stableHost`. -/
theorem host_eventually_eq_stableHost [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    (hna : ¬ ∃ᶠ k in atTop, stableHost hs hr ∈ (mda.run as k).accept) :
    ∃ k, ∀ n, shortestHostPos hs hr k ≤ n → host hs hr n = stableHost hs hr := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (not_frequently.1 hna)
  obtain ⟨hmono, -, -⟩ := shortestHostPos_spec hs hr
  set f := shortestHostPos hs hr
  set n0 := shortestHostStart hs hr
  refine ⟨n0 + N, fun n hn => ?_⟩
  have hT : f n0 ≤ f (n0 + N) := hmono.monotone (Nat.le_add_right _ _)
  have hNle : N ≤ f (n0 + N) := (Nat.le_add_left N n0).trans (hmono.id_le _)
  -- backward induction: if the host is `stableHost` at time `m + d`, it is so at time `m`
  have key : ∀ d m, f (n0 + N) ≤ m →
      host hs hr (m + d) = stableHost hs hr → host hs hr m = stableHost hs hr := by
    intro d
    induction d with
    | zero => intro m _ h; exact h
    | succ d ih =>
      intro m hm h
      have h1 : host hs hr (m + 1) = stableHost hs hr :=
        ih (m + 1) (hm.trans (Nat.le_succ m)) (by rwa [Nat.add_right_comm, Nat.add_assoc])
      exact host_eq_stableHost_of_succ hs hr (hT.trans hm)
        (hN _ (hNle.trans (hm.trans (Nat.le_succ m)))) h1
  have hm : n ≤ f (n0 + n) := (Nat.le_add_left n n0).trans (hmono.id_le _)
  refine key (f (n0 + n) - n) n hn ?_
  rw [Nat.add_sub_cancel' hm]
  exact host_shortestHostPos hs hr (Nat.le_add_right _ _)

/-- If the run `ss` of `na` visits accepting states infinitely often, then `stableHost` is
accepting infinitely often. -/
theorem stableHost_accept_frequently [Finite State] (hs : SafraSpec na mda) (hr : na.Run as ss)
    (ha : ∃ᶠ k in atTop, ss k ∈ na.accept) :
    ∃ᶠ k in atTop, stableHost hs hr ∈ (mda.run as k).accept := by
  by_contra hna
  obtain ⟨k, hk⟩ := host_eventually_eq_stableHost hs hr hna
  set p := shortestHostPos hs hr k
  obtain ⟨N, hN⟩ := eventually_atTop.1 (not_frequently.1 hna)
  obtain ⟨t1, ht1, hfin⟩ := frequently_atTop.1 ha (p + N + 1)
  obtain ⟨t, rfl⟩ : ∃ t, t1 = t + 1 := ⟨t1 - 1, by lia⟩
  have ht : host hs hr t = stableHost hs hr := hk t (by lia)
  have ht' : host hs hr (t + 1) = stableHost hs hr := hk (t + 1) (by lia)
  obtain ⟨h1, -⟩ := hs.forward (mda.run as t) (as t) (ss t) (ss (t + 1))
    (state_mem_macro_states hs hr t) (state_mem_macro_states hs hr (t + 1)) (hr.trans t)
  rcases h1 with ⟨-, hne⟩ | ⟨-, ha'⟩
  · have hne' : host hs hr (t + 1) ≠ host hs hr t := hne hfin
    exact hne' (ht'.trans ht.symm)
  · change host hs hr (t + 1) ∈ (mda.run as (t + 1)).accept at ha'
    rw [ht'] at ha'
    exact hN (t + 1) (by lia) ha'

/-- The "only if" part of Proposition 1 of Schewe's paper: every word accepted by the Büchi
automaton `na` is accepted by the Rabin automaton `mda`. -/
theorem safraSpec_complete [Finite State] (hs : SafraSpec na mda)
    (h : Accepts na as) : Accepts mda as := by
  obtain ⟨ss, hr, ha⟩ := h
  refine ⟨({ms | stableHost hs hr ∈ ms.accept}, {ms | stableHost hs hr ∉ ms.stableTree}),
    by rw [hs.pairs]; exact ⟨stableHost hs hr, rfl⟩, ?_, ?_⟩
  · exact stableHost_accept_frequently hs hr ha
  · refine eventually_atTop.2 ⟨stableHostStart hs hr, fun k hk => ?_⟩
    have := stableHost_stable hs hr (k - stableHostStart hs hr)
    rw [Nat.add_sub_cancel' hk] at this
    simpa using this

end Cslib.SafraConstruction
