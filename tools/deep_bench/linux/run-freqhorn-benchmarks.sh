#!/usr/bin/env bash

set -e

# Get IP addresses
# HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_FreqHornPlatform_Linux\[\] | sed -e 's/^/1\/ubuntu@/' | xargs echo -n | tr '\n' ','`
HOSTS=`../scripts/ec2-inv.py --list | jq -r .tag_FreqHornPlatform_Linux\[\] | sed -e 's/^/1\/ssh -i ~\/.ssh\/deephornec2.pem ubuntu@/' | tr '\n' ','`
echo $HOSTS

# Disable StrictHostKeyChecking temporarily. (So hacky.)
touch ~/.ssh/config
cp ~/.ssh/config ~/.ssh/config.backup
(echo 'Host *'; echo StrictHostKeyChecking no) >> ~/.ssh/config

# Update pass: git pull, make, etc.
# parallel --nonall --sshlogin $HOSTS \
#   "git config --global user.email \"emrysk@gmail.com\" && " \
#   "git config --global user.name \"Sam Kaufman\" && " \
#   "cd /home/ubuntu/aeval && " \
#   "git clean -fd && " \
#   "git stash && " \
#   "git pull && " \
#   "git checkout rnd-parallel-master-slave && " \
#   "cd build && " \
#   "make"

# TODO: rsync & re-build (instead of prior update pass)

# Run the jobs
../scripts/all-jobs.py freqhorn | parallel \
  --resume-failed \
  --joblog ./clusterjobs.log \
  --return "out-{2}-{3}--{4}--i{5}.tar.gz" \
  --cleanup \
  --colsep ':::' \
  -a - \
  --sshlogin "$HOSTS" \
  "rm -rf out && " \
  "mkdir out && " \
  "cd /home/ubuntu/aeval/tools/deep_bench/scripts && " \
  "FREQHORN_ROOT=/home/ubuntu/aeval FREQHORN_BENCH=/home/ubuntu/aeval/bench_horn ./benchmark-supervisor.py -o /home/ubuntu/out {1} {4} {3} {2} &> /home/ubuntu/out/supervisor.std.log ; " \
  "cd /home/ubuntu ; " \
  "tar -zcf out-{2}-{3}--{4}--i{5}.tar.gz out/ ;"

# Remove the disabling of StrictHostKeyChecking
mv ~/.ssh/config.backup ~/.ssh/config
