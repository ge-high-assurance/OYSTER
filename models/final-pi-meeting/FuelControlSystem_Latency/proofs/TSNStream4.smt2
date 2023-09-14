(set-logic QF_LIA)
(declare-fun latency () Int)
(declare-fun threshold () Int)
(declare-fun start_time () Int)
(declare-fun formula () Int)
(declare-fun arrival_time () Int)
(declare-fun arrival_limit () Int)
(assert (= start_time 5500000))
(assert (= threshold 200))
(assert (= arrival_limit 6000000))
(assert (>= arrival_time (+ arrival_limit threshold)))

(declare-fun GPM_R2_link_delay  () Int)
(declare-fun GPM_R2_propagation_delay  () Int)
(declare-fun GPM_R2_tas_jitter  () Int)
(assert (= GPM_R2_link_delay 8))
(assert (= GPM_R2_propagation_delay 10))
(assert (= GPM_R2_tas_jitter 200))
(declare-fun ACS_R2_egress_delay  () Int)
(declare-fun ACS_R2_fabric_delay  () Int)
(declare-fun ACS_R2_ingress_delay  () Int)
(declare-fun ACS_R2_tas_jitter  () Int)
(assert (= ACS_R2_egress_delay 9))
(assert (= ACS_R2_fabric_delay 1008))
(assert (= ACS_R2_ingress_delay 9))
(assert (= ACS_R2_tas_jitter 100))
(declare-fun RDC_R1_link_delay  () Int)
(declare-fun RDC_R1_propagation_delay  () Int)
(declare-fun RDC_R1_tas_jitter  () Int)
(assert (= RDC_R1_link_delay 8))
(assert (= RDC_R1_propagation_delay 10))
(assert (= RDC_R1_tas_jitter 200))
(declare-fun R_Eng_SO_Valve_link_delay  () Int)
(declare-fun R_Eng_SO_Valve_propagation_delay  () Int)
(declare-fun R_Eng_SO_Valve_tas_jitter  () Int)
(assert (= R_Eng_SO_Valve_link_delay 8))
(assert (= R_Eng_SO_Valve_propagation_delay 10))
(assert (= R_Eng_SO_Valve_tas_jitter 200))
(assert (= latency (+ GPM_R2_link_delay
GPM_R2_propagation_delay
GPM_R2_tas_jitter
ACS_R2_egress_delay
ACS_R2_fabric_delay
ACS_R2_ingress_delay
ACS_R2_tas_jitter
RDC_R1_link_delay
RDC_R1_propagation_delay
RDC_R1_tas_jitter
R_Eng_SO_Valve_link_delay
R_Eng_SO_Valve_propagation_delay
R_Eng_SO_Valve_tas_jitter
)))
(assert (= arrival_time (+ start_time latency)))
(check-sat)
