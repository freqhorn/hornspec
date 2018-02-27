#!/usr/bin/env bash

set -e

HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_FreqHornPlatform_Windows\[\] | sed -e 's/^/1\/Administrator@/' | xargs echo -n | tr '\n' ','`
# HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_Project_FreqHorn\[\] | sed -e 's/^/1\/ssh -o StrictHostKeyChecking=no Administrator@/' | xargs echo -n | tr '\n' ','`
echo $HOSTS

echo ""
echo "Starting jobs. (If this seems to hang, make sure you've used ssh-add"
echo "on your key.)"
echo ""

# Disable StrictHostKeyChecking temporarily. (Hacky and brittle.)
touch ~/.ssh/config
cp ~/.ssh/config ~/.ssh/config.backup
(echo 'Host *'; echo StrictHostKeyChecking no) >> ~/.ssh/config

# find ../../../bench_horn/*.smt2 -exec basename {} .smt2 \; | parallel \
./all-jobs.py freqhorn | parallel \
  --resume-failed \
  --joblog ./clusterjobs.log \
  --return "out-{2}-{3}--{4}--i{5}.tar.gz" \
  --colsep ':::' \
  --cleanup \
  -a - \
  --sshlogin "$HOSTS" \
  "cd ~ && " \
  "rm -rf out && " \
  "mkdir out && " \
  "MCMC_ROOT=/cygdrive/c/MCMC ICE_ROOT=/cygdrive/c/ICE MCMC_BENCH=/cygdrive/c/bench_horn_mcmc ICE_BENCH=/cygdrive/c/bench_horn_ice Z3_ROOT=/cygdrive/c/tools/cygwin/home/Administrator/spacer/build Z3_BENCH=/cygdrive/c/bench_horn /cygdrive/c/benchmark-supervisor.py -o /home/ubuntu/out {1} {4} {3} {2} &> out/supervisor.std.log ; " \
  "cd ~ ; " \
  "tar -zcf out-{2}-{3}--{4}--i{5}.tar.gz out/ ;"
  ::: mcmc ice z3 ::: {0..2}

# Remove the disabling of StrictHostKeyChecking
mv ~/.ssh/config.backup ~/.ssh/config
