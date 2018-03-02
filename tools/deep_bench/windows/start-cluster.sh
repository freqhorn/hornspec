#!/bin/bash

set -e

export OBJC_DISABLE_INITIALIZE_FORK_SAFETY=YES

# Spin up cluster/wait for connection
if [[ $1 != "--provision" ]]
then
    cd terraform
    terraform apply
    cd ../ansible
    ansible -i ../../scripts/ec2-inv.py -i inventory windows -m wait_for_connection
else
    cd ansible
fi

# Provision machines
ansible-playbook -i ../../scripts/ec2-inv.py -i inventory playbook.yml
cd ..
