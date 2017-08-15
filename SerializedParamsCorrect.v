Require Import StructTact.Util.
Require Import Verdi.Verdi.

Require Import FunctionalExtensionality.

Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.

Require Import Cheerios.Cheerios.
Require Import VerdiCheerios.SerializedParams.

Require Import mathcomp.ssreflect.ssreflect.

Section SerializedCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {orig_name_overlay_params : NameOverlayParams orig_multi_params}.
  Context {orig_fail_msg_params : FailMsgParams orig_multi_params}.
  Context {orig_new_msg_params : NewMsgParams orig_multi_params}.

  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  (* total map simulations *)

  Definition serialize_packet p :=
    @mkPacket _ serialized_multi_params
              (@pSrc _ orig_multi_params p)
              (pDst p)
              (serialize_top (serialize (pBody p))).

  Definition serialize_net (net : @network _ orig_multi_params) : (@network _ serialized_multi_params) :=
    @mkNetwork _ serialized_multi_params (map serialize_packet (nwPackets net)) net.(nwState).

  Definition serialize_trace_occ (e : @name _ orig_multi_params * (@input orig_base_params + list (@output orig_base_params))) :
    @name _ serialized_multi_params * (@input serialized_base_params + list (@output serialized_base_params)) :=
  let (n, s) := e in
  match s with
  | inl io => (n, inl (serialize_top (serialize io)))
  | inr lo => (n, inr (map (fun v => serialize_top (serialize v)) lo))
  end.

  Definition serialize_onet (net : @ordered_network _ orig_multi_params) : (@ordered_network _ serialized_multi_params) :=
    @mkONetwork _ serialized_multi_params (fun src dst => map (fun v => serialize_top (serialize v)) (net.(onwPackets) src dst)) net.(onwState).

  Definition serialize_odnet (net : @ordered_dynamic_network _ orig_multi_params) : (@ordered_dynamic_network _ serialized_multi_params) :=
    @mkODNetwork _ serialized_multi_params net.(odnwNodes) (fun src dst => map (fun v => serialize_top (serialize v)) (net.(odnwPackets) src dst)) net.(odnwState).

  Definition serialize_trace_ev (e : @name _ orig_multi_params * (@input orig_base_params + (@output orig_base_params))) :=
    match e with
    | (n, inl i) => (n, inl (serialize_top (serialize i)))
    | (n, inr o) => (n, inr (serialize_top (serialize o)))
    end.

  Instance orig_multi_params_name_tot_map :
    MultiParamsNameTotalMap orig_multi_params serialized_multi_params :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

  Instance orig_multi_params_name_tot_map_bijective :
    MultiParamsNameTotalMapBijective orig_multi_params_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => eq_refl ;
    tot_map_name_inverse_inv := fun _ => eq_refl
  }.

  Instance orig_base_params_tot_map :
    BaseParamsTotalMap orig_base_params serialized_base_params :=
  {
    tot_map_data := id;
    tot_map_input := fun v => serialize_top (serialize v);
    tot_map_output := fun v => serialize_top (serialize v)
  }.

  Instance orig_multi_params_tot_msg_map :
    MultiParamsMsgTotalMap orig_multi_params serialized_multi_params :=
  {
    tot_map_msg := fun v => serialize_top (serialize v)
  }.

  Instance orig_failure_params_tot_map_congruency : FailureParamsTotalMapCongruency orig_failure_params serialized_failure_params orig_base_params_tot_map :=
    {
      tot_reboot_eq := fun _ => eq_refl
    }.

  Instance orig_multi_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency orig_name_overlay_params serialized_name_overlay_params orig_multi_params_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

  Instance orig_multi_fail_msg_params_tot_map_congruency : FailMsgParamsTotalMapCongruency orig_fail_msg_params serialized_fail_msg_params orig_multi_params_tot_msg_map :=
  {
    tot_fail_msg_fst_snd := eq_refl
  }.

  Instance orig_multi_new_msg_params_tot_map_congruency : NewMsgParamsTotalMapCongruency orig_new_msg_params serialized_new_msg_params orig_multi_params_tot_msg_map :=
  {
    tot_new_msg_fst_snd := eq_refl
  }.

  Instance orig_multi_params_map_congruency :
    MultiParamsTotalMapCongruency orig_base_params_tot_map
      orig_multi_params_name_tot_map orig_multi_params_tot_msg_map :=
  {
    tot_init_handlers_eq := fun _ => eq_refl ;
    tot_net_handlers_eq := _ ;
    tot_input_handlers_eq := _
  }.
  Proof.
  - move => me src m st.
    rewrite /tot_mapped_net_handlers /= /tot_map_name_msgs /= /id /=.
    repeat break_let.
    rewrite /serialized_net_handlers.
    rewrite serialize_deserialize_top_id.
    rewrite /serialize_handler_result.
    repeat break_let.
    find_injection.
    set l1 := map _ l.
    set l2 := map _ l.
    suff H_suff: l1 = l2 by rewrite H_suff.
    rewrite /l1 /l2.
    clear.
    elim: l => //=.
    move => p l IH.
    rewrite IH /= /serialize_name_msg_tuple /=.
    by break_let.
  - move => me inp st.
    rewrite /tot_mapped_input_handlers /=.
    repeat break_let.
    unfold serialized_input_handlers in *.
    rewrite serialize_deserialize_top_id.
    rewrite /serialize_handler_result /id /tot_map_name_msgs /tot_map_name /= /id /=.
    repeat break_let.
    find_injection.
    set l1 := map _ l.
    set l2 := map _ l.
    suff H_suff: l1 = l2 by rewrite H_suff.
    rewrite /l1 /l2.
    clear.
    elim: l => //=.
    move => p l IH.
    rewrite IH /= /serialize_name_msg_tuple /=.
    by break_let.
  Qed.

  Lemma serialize_odnet_tot_map_odnet :
    forall net, serialize_odnet net = tot_map_odnet net.
  Proof.
  move => net.
  rewrite /tot_map_odnet.
  rewrite /tot_map_name /= /id /= map_id.
  rewrite /serialize_odnet.
  set f := fun _ => match _ with _ => _ end.
  by have ->: odnwState net = f by rewrite /f; apply functional_extensionality => n; case: odnwState.
  Qed.

  Lemma step_async_serialize_simulation :
    forall net net' tr,
      @step_async _ orig_multi_params net net' tr ->
      @step_async _ serialized_multi_params (serialize_net net) (serialize_net net') (map serialize_trace_occ tr).
  Proof.
  move => net net' out H_step.
  apply step_async_tot_mapped_simulation_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  set fp := fun p => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  by rewrite H_eq {H_eq fp}. 
  Qed.

  Lemma step_async_serialize_simulation_star :
    forall net tr,
      @step_async_star _ orig_multi_params step_async_init net tr ->
      @step_async_star _ serialized_multi_params step_async_init (serialize_net net) (map serialize_trace_occ tr).
  Proof.
  move => net tr H_step.
  apply step_async_tot_mapped_simulation_star_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  by rewrite H_eq {H_eq fp}. 
  Qed.

  Lemma step_failure_serialize_simulation :
    forall net net' failed failed' tr,
      @step_failure _ _ orig_failure_params (failed, net) (failed', net') tr ->
      @step_failure _ _ serialized_failure_params (failed, serialize_net net) (failed', serialize_net net') (map serialize_trace_occ tr).
  Proof.
  move => net net' failed failed' tr H_step.
  apply step_failure_tot_mapped_simulation_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  rewrite 2!map_id.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  by rewrite H_eq {H_eq fp}. 
  Qed.

  Lemma step_failure_serialize_simulation_star :
    forall net failed tr,
      @step_failure_star _ _ orig_failure_params step_failure_init (failed, net) tr ->
      @step_failure_star _ _ serialized_failure_params step_failure_init (failed, serialize_net net) (map serialize_trace_occ tr).
  Proof.
  move => net failed tr H_step.
  apply step_failure_tot_mapped_simulation_star_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  rewrite map_id.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.  
  by rewrite H_eq {H_eq fp}.
  Qed.  

  Lemma step_ordered_failure_serialize_simulation :
  forall net net' failed failed' tr,
    @step_ordered_failure _ _ orig_name_overlay_params orig_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_failure _ _ serialized_name_overlay_params serialized_fail_msg_params (failed, serialize_onet net) (failed', serialize_onet net') (map serialize_trace_ev tr).
  Proof.
  move => net net' failed failed' tr H_step.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  exact: step_ordered_failure_tot_mapped_simulation_1.
  Qed.

  Lemma step_ordered_failure_serialize_simulation_star :
  forall net failed tr,
    @step_ordered_failure_star _ _ orig_name_overlay_params orig_fail_msg_params step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ serialized_name_overlay_params serialized_fail_msg_params step_ordered_failure_init (failed, serialize_onet net) (map serialize_trace_ev tr).
  Proof.
  move => net failed tr H_st.
  have ->: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  exact: step_ordered_failure_tot_mapped_simulation_star_1.
  Qed.

  Lemma step_ordered_dynamic_failure_serialize_simulation :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params (failed, serialize_odnet net) (failed', serialize_odnet net') (map serialize_trace_ev tr).
  Proof.
  move => net net' failed failed' tr H_nd H_step.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  rewrite 2!serialize_odnet_tot_map_odnet.
  exact: step_ordered_dynamic_failure_tot_mapped_simulation_1.
  Qed.

  Lemma step_ordered_dynamic_failure_serialize_simulation_star :
  forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params step_ordered_dynamic_failure_init (failed, serialize_odnet net) (map serialize_trace_ev tr).
  Proof.
  move => net failed tr H_st.
  have ->: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite serialize_odnet_tot_map_odnet.
  exact: step_ordered_dynamic_failure_tot_mapped_simulation_star_1.
  Qed.

  (* partial map simulation *)

  Definition deserialize_packet (p : @packet _ serialized_multi_params) : option (@packet _ orig_multi_params) :=
    match deserialize_top deserialize (pBody p) with
    | None => None
    | Some body =>
      Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body)
    end.

  Definition deserialize_net (net: @network _ serialized_multi_params) :  (@network _ orig_multi_params) :=
    @mkNetwork _ orig_multi_params (filterMap deserialize_packet (nwPackets net)) net.(nwState).

  Definition deserialize_onet (net: @ordered_network _ serialized_multi_params) :  (@ordered_network _ orig_multi_params) :=
    @mkONetwork _ orig_multi_params (fun src dst => filterMap (fun m => match deserialize_top deserialize m with Some data => Some data | None => None end) (net.(onwPackets) src dst)) net.(onwState).

  Definition deserialize_odnet (net: @ordered_dynamic_network _ serialized_multi_params) :  (@ordered_dynamic_network _ orig_multi_params) :=
    @mkODNetwork _ orig_multi_params net.(odnwNodes) (fun src dst => filterMap (fun m => match deserialize_top deserialize m with Some data => Some data | None => None end) (net.(odnwPackets) src dst)) net.(odnwState).

  Definition deserialize_trace_occ (e : @name _ serialized_multi_params * (@input serialized_base_params + list (@output serialized_base_params))) :
    option (@name _ orig_multi_params * (@input orig_base_params + list (@output orig_base_params))) :=
  let (n, s) := e in
  match s with
  | inl i => 
    match deserialize_top deserialize i with
    | Some data => Some (n, inl data)
    | None => None
    end
  | inr lo => Some (n, inr (filterMap (fun o => match deserialize_top deserialize o with Some data => Some data | None => None end) lo))
  end.

  Definition deserialize_trace_ev (e : @name _ serialized_multi_params * (@input serialized_base_params + @output serialized_base_params)) :
    option (@name _ orig_multi_params * (@input orig_base_params + @output orig_base_params)) :=
   match e with
   | (n, inl i) => 
     match deserialize_top deserialize i with
     | Some data => Some (n, inl data)
     | None => None
     end
   | (n, inr o) =>
      match deserialize_top deserialize o with
      | Some data => Some (n, inr data)
      | None => None
      end
   end.

  Lemma deserialize_serialize_net_id : forall net,
      deserialize_net (serialize_net net) = net.
  Proof.
  case => ps nwS.
  rewrite /deserialize_net /serialize_net /=.
  set ps' := filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    rewrite /deserialize_packet.
    elim: ps => [|p ps IH] //=.
    rewrite serialize_deserialize_top_id IH.
    by case: p.
  by rewrite H_p.
  Qed.

  Lemma deserialize_serialize_onet_id : forall net,
      deserialize_onet (serialize_onet net) = net.
  Proof.
  case => ps s.
  rewrite /deserialize_onet /serialize_onet /=.
  set ps' := fun _ _ => filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.
    elim: (ps src dst) => [|m ms IH] //=.
    by rewrite serialize_deserialize_top_id IH.
  by rewrite H_p.
  Qed.

  Lemma deserialize_serialize_odnet_id : forall net,
      deserialize_odnet (serialize_odnet net) = net.
  Proof.
  case => ns ps s.
  rewrite /deserialize_odnet /serialize_odnet /=.
  set ps' := fun _ _ => filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    apply functional_extensionality => src.
    apply functional_extensionality => dst.    
    elim: (ps src dst) => [|m ms IH] //=.
    by rewrite serialize_deserialize_top_id IH.
  by rewrite H_p.
  Qed.

  Lemma filterMap_deserialize_tr_occ_map_serialize_id :
    forall tr, filterMap deserialize_trace_occ (map serialize_trace_occ tr) = tr.
  Proof.
  elim => //=.
  case => n. 
  case => [i|o] l IH; rewrite /deserialize_trace_occ /serialize_trace_occ /=.
  - by rewrite serialize_deserialize_top_id /= IH.
  - rewrite IH.
    set fMo := filterMap _ _.
    suff H_suff: fMo = o by rewrite H_suff.
    rewrite /fMo.
    clear.
    elim: o => //=.
    move => o l IH.
    by rewrite serialize_deserialize_top_id /= IH.
  Qed.

  Lemma filterMap_deserialize_trace_map_serialize_id :
    forall tr, filterMap deserialize_trace_ev (map serialize_trace_ev tr) = tr.
  Proof.
  elim => //=.
  case => n. 
  case => [i|o] l IH /=.
  - by rewrite serialize_deserialize_top_id IH.
  - by rewrite serialize_deserialize_top_id IH.
  Qed.

  Instance multi_params_orig_name_tot_map :
    MultiParamsNameTotalMap serialized_multi_params orig_multi_params :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

  Instance multi_params_orig_name_tot_map_bijective :
    MultiParamsNameTotalMapBijective multi_params_orig_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => eq_refl ;
    tot_map_name_inverse_inv := fun _ => eq_refl
  }.

  Instance multi_orig_params_pt_msg_map : MultiParamsMsgPartialMap serialized_multi_params orig_multi_params :=
  {
    pt_map_msg := fun m => 
      match deserialize_top deserialize m with
      | Some data => Some data
      | None => None
      end   
  }.

  Instance multi_orig_base_params_pt_map : BaseParamsPartialMap serialized_base_params orig_base_params :=
  {
    pt_map_data := id;
    pt_map_input := fun i =>
                     match deserialize_top deserialize i with
                     | Some data => Some data
                     | None => None
                     end;
    pt_map_output := fun o =>
                     match deserialize_top deserialize o with
                     | Some data => Some data
                     | None => None
                     end
  }.

  Instance multi_orig_failure_params_pt_map_congruency : FailureParamsPartialMapCongruency serialized_failure_params orig_failure_params multi_orig_base_params_pt_map :=
    {
      pt_reboot_eq := fun _ => eq_refl
    }.

  Instance multi_orig_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency serialized_name_overlay_params orig_name_overlay_params multi_params_orig_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

  Instance multi_orig_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency serialized_fail_msg_params orig_fail_msg_params multi_orig_params_pt_msg_map :=
  {
    pt_fail_msg_fst_snd := _
  }.
  Proof.
  rewrite /pt_map_msg /=.
  by rewrite serialize_deserialize_top_id.
  Qed.

  Instance multi_orig_new_msg_params_pt_map_congruency : NewMsgParamsPartialMapCongruency serialized_new_msg_params orig_new_msg_params multi_orig_params_pt_msg_map :=
  {
    pt_new_msg_fst_snd := _
  }.
  Proof.
  rewrite /pt_map_msg /=.
  by rewrite serialize_deserialize_top_id.
  Qed.

  Instance multi_orig_params_pt_map_congruency : MultiParamsPartialMapCongruency multi_orig_base_params_pt_map multi_params_orig_name_tot_map multi_orig_params_pt_msg_map :=
  {
    pt_init_handlers_eq := fun _ => eq_refl ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
  Proof.
  - move => me src mg st mg' H_eq.
    rewrite /pt_mapped_net_handlers.
    repeat break_let.
    rewrite /tot_map_name /= /id.
    rewrite /pt_map_msg /= in H_eq.
    rewrite /net_handlers /= /serialized_net_handlers in Heqp.
    move: H_eq Heqp.
    case H_m: (deserialize_top deserialize mg) => [m'|] => H_eq //.
    find_injection.
    rewrite /serialize_handler_result in Heqp.
    repeat break_let.
    find_injection.
    set sl2 := filterMap (fun _ => _) _.
    set sl1 := filterMap _ _.
    have H_eq: sl2 = l2.
      rewrite /sl2.
      clear.
      elim: l2 => //=.
      move => o l IH.
      by rewrite serialize_deserialize_top_id IH.
    have H_eq': sl1 = l1.
      rewrite /sl1 /pt_map_name_msg /tot_map_name /id /= /id /serialize_name_msg_tuple.
      clear.
      elim: l1 => //=.
      case => [n m] => /=.
      move => l IH.
      by rewrite serialize_deserialize_top_id IH.
    by rewrite H_eq H_eq'.
  - move => me src mg st out st' ps H_eq H_eq'.
    rewrite /net_handlers /= /serialized_net_handlers /= in H_eq'.
    rewrite /pt_map_msg /= in H_eq.
    move: H_eq H_eq'.
    case H_eq_m: (deserialize_top deserialize mg) => [mg'|] H_eq H_eq'; first by repeat break_let.
    by find_injection.
  - move => me inp st inp' H_eq.
    rewrite /pt_mapped_input_handlers.
    repeat break_let.
    rewrite /tot_map_name /= /id.
    rewrite /pt_map_input /= in H_eq.
    rewrite /input_handlers /= /serialized_input_handlers in Heqp.
    move: H_eq Heqp.
    case H_m: (deserialize_top deserialize inp) => [i|] => H_eq //.
    find_injection.
    rewrite /serialize_handler_result in Heqp.
    repeat break_let.
    find_injection.
    set sl2 := filterMap (fun _ => _) _.
    set sl1 := filterMap _ _.
    have H_eq: sl2 = l2.
      rewrite /sl2.
      clear.
      elim: l2 => //=.
      move => o l IH.
      by rewrite serialize_deserialize_top_id IH.
    have H_eq': sl1 = l1.
      rewrite /sl1 /pt_map_name_msg /tot_map_name /id /= /id /serialize_name_msg_tuple.
      clear.
      elim: l1 => //=.
      case => [n m] => /=.
      move => l IH.
      by rewrite serialize_deserialize_top_id IH.
    by rewrite H_eq H_eq'.
  - move => me inp st out st' ps H_eq H_eq'.
    rewrite /input_handlers /= /serialized_input_handlers /= in H_eq'.
    rewrite /pt_map_msg /= in H_eq.
    move: H_eq H_eq'.
    case H_eq_m: (deserialize_top deserialize inp) => [i|] H_eq H_eq'; first by repeat break_let.
    by find_injection.
  Qed.

  Lemma pt_map_trace_occ_filterMap :
    forall tr, filterMap pt_map_trace_occ tr = filterMap deserialize_trace_occ tr.
  Proof.
  rewrite /pt_map_trace_occ /tot_map_name /= /deserialize_packet.
  elim => //=.
  case => n.
  case => [i|o] l IH; last by rewrite -IH.
  rewrite -IH /pt_map_trace_occ /pt_map_input /= /deserialize_trace_occ /=.
  by case: (deserialize_top deserialize _).
  Qed.

  Lemma pt_map_trace_ev_filterMap :
    forall tr, filterMap pt_map_trace_ev tr = filterMap deserialize_trace_ev tr.
  Proof.
  rewrite /pt_map_trace_ev /tot_map_name /=.
  elim => //=.
  case => n.
  case => [i|o] l IH.
  - rewrite -IH /pt_map_trace_ev /pt_map_input /= /deserialize_trace_ev /=.
    by case: (deserialize_top deserialize _).
  - rewrite -IH /pt_map_trace_ev /pt_map_output /= /deserialize_trace_ev /= /id /=.
    by case: (deserialize_top deserialize _).
  Qed.

  Lemma pt_map_net_deserialize_net : 
    forall net, pt_map_net net = deserialize_net net.
  Proof.
  move => net.
  rewrite /deserialize_net.
  rewrite /pt_map_net /pt_map_data /= /id /= /pt_map_packet.
  set fm := filterMap _ _.
  set fm' := filterMap _ _.
  suff H_eq: fm = fm' by rewrite H_eq.
  rewrite /fm /fm'.
  clear.
  rewrite /pt_map_packet /tot_map_name /= /deserialize_packet.
  elim (nwPackets net) => //=.
  case => [src dst body] /= l IH.
  rewrite IH.
  by case (deserialize_top deserialize _).
  Qed.

  Lemma pt_map_onet_deserialize_onet : 
    forall net, pt_map_onet net = deserialize_onet net.
  Proof. by []. Qed.
  
  Lemma pt_map_odnet_deserialize_odnet : 
    forall net, pt_map_odnet net = deserialize_odnet net.
  Proof.
  move => net.
  rewrite /deserialize_odnet.
  rewrite /pt_map_odnet /pt_map_data /= /id /= /pt_map_msg.
  set fm := fun _ _ => filterMap _ _.
  rewrite map_id.
  set s := fun _ => match _ with _ => _ end.
  have H_eq: odnwState net = s.
    rewrite /s.
    apply functional_extensionality => n.
    by case: odnwState.
  by rewrite H_eq.
  Qed.

  Lemma step_async_deserialized_simulation :
  forall net net' tr,
    @step_async _ serialized_multi_params net net' tr ->
    @step_async _ orig_multi_params (deserialize_net net) (deserialize_net net') (filterMap deserialize_trace_occ tr) \/ 
    (deserialize_net net' = deserialize_net net /\ filterMap trace_non_empty_out (filterMap deserialize_trace_occ tr) = []).
  Proof.
  move => net net' tr H_st.
  rewrite -pt_map_trace_occ_filterMap -2!pt_map_net_deserialize_net.
  exact: step_async_pt_mapped_simulation_1.
  Qed.

  Lemma step_async_deserialized_simulation_star :
  forall net tr,
    @step_async_star _ serialized_multi_params step_async_init net tr ->
    exists tr', @step_async_star _ orig_multi_params step_async_init (deserialize_net net) tr' /\ 
     filterMap trace_non_empty_out (filterMap deserialize_trace_occ tr) = filterMap trace_non_empty_out tr'.
  Proof.
  move => net tr H_st.
  apply step_async_pt_mapped_simulation_star_1 in H_st.
  break_exists.
  break_and.
  exists x.
  by rewrite -pt_map_trace_occ_filterMap -pt_map_net_deserialize_net.
  Qed.

  Lemma step_failure_deserialized_simulation :
  forall net net' failed failed' tr,
    @step_failure _ _ serialized_failure_params (failed, net) (failed', net') tr ->
    @step_failure _ _ orig_failure_params (failed, deserialize_net net) (failed', deserialize_net net') (filterMap deserialize_trace_occ tr) \/ 
    (deserialize_net net' = deserialize_net net /\ failed = failed' /\ filterMap trace_non_empty_out (filterMap deserialize_trace_occ tr) = []).
  Proof.
  move => net net' failed failed' tr H_st.
  rewrite -pt_map_trace_occ_filterMap -2!pt_map_net_deserialize_net.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  exact: step_failure_pt_mapped_simulation_1.
  Qed.

  Lemma step_failure_deserialized_simulation_star :
  forall net failed tr,
    @step_failure_star _ _ serialized_failure_params step_failure_init (failed, net) tr ->
    exists tr', @step_failure_star _ _ orig_failure_params step_failure_init (failed, deserialize_net net) tr' /\ 
     filterMap trace_non_empty_out (filterMap deserialize_trace_occ tr) = filterMap trace_non_empty_out tr'.
  Proof.
  move => net failed tr H_st.
  apply step_failure_pt_mapped_simulation_star_1 in H_st.
  break_exists.
  break_and.
  exists x.
  rewrite -pt_map_trace_occ_filterMap -pt_map_net_deserialize_net.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  by rewrite {1}H_eq_n.
  Qed.

  Lemma step_ordered_failure_deserialized_simulation :
    forall net net' failed failed' tr,
      @step_ordered_failure _ _ serialized_name_overlay_params serialized_fail_msg_params (failed, net) (failed', net') tr ->
      @step_ordered_failure _ _ orig_name_overlay_params orig_fail_msg_params (failed, deserialize_onet net) (failed', deserialize_onet net') (filterMap deserialize_trace_ev tr) \/
      deserialize_onet net = deserialize_onet net' /\ failed = failed' /\ filterMap deserialize_trace_ev tr = [].
  Proof.   
  move => net net' failed failed' tr H_st.
  eapply step_ordered_failure_pt_mapped_simulation_1 in H_st.
  case: H_st => H_st.
    have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n.
    have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n'.
    left.
    rewrite -2!pt_map_onet_deserialize_onet.
    rewrite -pt_map_trace_ev_filterMap.
    exact: H_st.
  right.
  break_and.
  by rewrite -2!pt_map_onet_deserialize_onet -pt_map_trace_ev_filterMap.
  Qed.

  Lemma step_ordered_failure_serialized_simulation_star :
    forall net failed tr,
    @step_ordered_failure_star _ _ serialized_name_overlay_params serialized_fail_msg_params step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ orig_name_overlay_params orig_fail_msg_params step_ordered_failure_init (failed, deserialize_onet net) (filterMap deserialize_trace_ev tr).
  Proof.
  move => onet failed tr H_st.
  apply step_ordered_failure_pt_mapped_simulation_star_1 in H_st.
  rewrite -pt_map_onet_deserialize_onet -pt_map_trace_ev_filterMap.
  by rewrite map_id in H_st.
  Qed.

  Lemma step_ordered_dynamic_failure_deserialized_simulation :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params (failed, deserialize_odnet net) (failed', deserialize_odnet net') (filterMap deserialize_trace_ev tr) \/
    deserialize_odnet net = deserialize_odnet net' /\ failed = failed' /\ filterMap deserialize_trace_ev tr = [].
  Proof.
  move => net net' failed failed' tr H_nd H_st.
  eapply step_ordered_dynamic_failure_pt_mapped_simulation_1 in H_st; last by [].
  case: H_st => H_st.
    have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n.
    have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
    rewrite {1}H_eq_n'.
    left.
    rewrite -2!pt_map_odnet_deserialize_odnet.
    rewrite -pt_map_trace_ev_filterMap.
    exact: H_st.
  right.
  break_and.
  by rewrite -2!pt_map_odnet_deserialize_odnet -pt_map_trace_ev_filterMap.
  Qed.

  Theorem step_ordered_dynamic_failure_dserialized_simulation_star :
    forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params step_ordered_dynamic_failure_init (failed, deserialize_odnet net) (filterMap deserialize_trace_ev tr).
  Proof.
  move => onet failed tr H_st.
  apply step_ordered_dynamic_failure_pt_mapped_simulation_star_1 in H_st.
  rewrite map_id in H_st.
  by rewrite -pt_map_odnet_deserialize_odnet -pt_map_trace_ev_filterMap.
  Qed.
End SerializedCorrect.
