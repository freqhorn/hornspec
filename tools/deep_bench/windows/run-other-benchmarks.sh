#!/usr/bin/env bash

set -e

HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_Project_FreqHorn\[\] | sed -e 's/^/1\/Administrator@/' | xargs echo -n | tr '\n' ','`
# HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_Project_FreqHorn\[\] | sed -e 's/^/1\/ssh -o StrictHostKeyChecking=no Administrator@/' | xargs echo -n | tr '\n' ','`
echo $HOSTS

# Disable StrictHostKeyChecking temporarily. (Hacky and brittle.)
touch ~/.ssh/config
cp ~/.ssh/config ~/.ssh/config.backup
(echo 'Host *'; echo StrictHostKeyChecking no) >> ~/.ssh/config

find ../../../bench_horn/*.smt2 -exec basename {} .smt2 \; | parallel \
  --resume-failed \
  --joblog ./clusterjobs.log \
  --return "out-{1}-{2}-i{3}.tar.gz" \
  --cleanup \
  --verbose \
  -a - \
  --sshlogin "$HOSTS" \
  "cd ~ && " \
  "rm -rf out && " \
  "mkdir out && " \
  "MCMC_ROOT=/cygdrive/c/MCMC ICE_ROOT=/cygdrive/c/ICE MCMC_BENCH=/cygdrive/c/bench_horn_mcmc ICE_BENCH=/cygdrive/c/bench_horn_ice /cygdrive/c/benchmark-others.py --logdir out/ -o out/times.json --{2} 1 {1} &> out/std.log ; " \
  "cd ~ ; " \
  "tar -zcf out-{1}-{2}-i{3}.tar.gz out/ ;" \
  ::: mcmc ice z3 ::: {0..9}

# Remove the disabling of StrictHostKeyChecking
mv ~/.ssh/config.backup ~/.ssh/config
