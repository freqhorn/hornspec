#!/usr/bin/env bash

set -e
set -x

# HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_FreqHornPlatform_Windows\[\] | sed -e 's/^/1\/Administrator@/' | xargs echo -n | tr '\n' ','`
HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_FreqHornPlatform_Windows\[\] | sed -e 's/^/1\/ssh -i ~\/.ssh\/freqhorn_rsa Administrator@/' | tr '\n' ','`
echo $HOSTS

echo ""
echo "Starting jobs. (If this seems to hang, make sure you've used ssh-add"
echo "on your key.)"
echo ""

# Disable StrictHostKeyChecking temporarily. (Hacky and brittle.)
touch ~/.ssh/config
cp ~/.ssh/config ~/.ssh/config.backup
(echo 'Host *'; echo StrictHostKeyChecking no) >> ~/.ssh/config

../scripts/all-jobs.py z3 | parallel \
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
  "MCMC_ROOT=/cygdrive/c/MCMC ICE_ROOT=/cygdrive/c/ICE MCMC_BENCH=/cygdrive/c/bench_horn_mcmc ICE_BENCH=/cygdrive/c/bench_horn_ice Z3_ROOT=/cygdrive/c/tools/cygwin/home/Administrator/spacer/build Z3_BENCH=/cygdrive/c/bench_horn /cygdrive/c/benchmark-supervisor.py -o ~/out {1} {4} {3} {2} &> out/supervisor.std.log ; " \
  "cd ~ ; " \
  "tar -zcf out-{2}-{3}--{4}--i{5}.tar.gz out/ ;"

# Remove the disabling of StrictHostKeyChecking
mv ~/.ssh/config.backup ~/.ssh/config
