#!/bin/bash

cp bpmn/auto-test/params-shipment.ml lib/encoding/manual_params.ml

echo "#################################"
echo "# Test petshop_shipment_focused #"
echo "#################################"
dune exec -- cocotreelo bpmn/simplified/petshop_shipment_focused.spthy bpmn/simplified/s2_leading.ctl -r 30 -c 1 -v -t

echo "#########################"
echo "# Test petshop_shipment #"
echo "#########################"
dune exec -- cocotreelo bpmn/simplified/petshop_shipment.spthy bpmn/simplified/s2_leading.ctl -r 30 -c 1 -v -t

cp bpmn/auto-test/params-credit-card.ml lib/encoding/manual_params.ml

echo "####################################"
echo "# Test petshop_credit_card_focused #"
echo "####################################"
dune exec -- cocotreelo bpmn/simplified/petshop_credit_card_focused.spthy bpmn/simplified/s2_leading.ctl -r 30 -c 1 -v -t

echo "############################"
echo "# Test petshop_credit_card #"
echo "############################"
dune exec -- cocotreelo bpmn/simplified/petshop_credit_card.spthy bpmn/simplified/s2_leading.ctl -r 30 -c 1 -v -t

echo "#########################"

cp bpmn/auto-test/params-complete.ml lib/encoding/manual_params.ml

echo "#########################"
echo "# Test petshop_complete #"
echo "#########################"
dune exec -- cocotreelo bpmn/simplified/petshop_complete.spthy bpmn/simplified/s2_leading.ctl -r 30 -c 1 -v -t
