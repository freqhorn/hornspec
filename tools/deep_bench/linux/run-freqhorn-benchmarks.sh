#!/usr/bin/env bash

set -x

cd terraform || exit 1
terraform apply || exit 1
cd ..

echo ""
echo "  Wait for the cluster to be up and running (not initializing)."
echo "  Then hit Enter to continue."
echo ""
read

# Get IP addresses
cd terraform || exit 1
terraform refresh || exit 1
SFR_ID=`jq -r ".modules[0].resources.\"aws_spot_fleet_request.fleet_req\".primary.id" terraform.tfstate`
INSTANCE_IDS=`aws ec2 describe-spot-fleet-instances --spot-fleet-request-id $SFR_ID | jq -r ".ActiveInstances[]|
select(.InstanceHealth==\"healthy\")|.InstanceId" | awk '{$1=$1};1'`
HOSTS=`aws ec2 describe-instances --instance-ids $INSTANCE_IDS | jq -r '.Reservations[0].Instances[].PublicIpAddress' | sed -e 's/^/1\/ubuntu@/' | xargs echo -n | tr ' ' ','`
echo $HOSTS
cd ..

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
find ../../bench_horn/*.smt2 -exec basename {} .smt2 \; | \
BENCH_MPIRUN=/usr/bin/mpirun parallel \
  --resume-failed \
  --joblog ./clusterjobs.log \
  --return "out-{1}-{2}-i{3}.tar.gz" \
  --cleanup \
  -a - \
  --env BENCH_MPIRUN \
  --sshlogin $HOSTS \
  "rm -rf out && " \
  "mkdir out && " \
  "cd /home/ubuntu/aeval/tools/deep_bench && " \
  "./benchmark-freqhorn.py -v -i 1 --logdir /home/ubuntu/out/benchlogs -o /home/ubuntu/out/ --hyper {2} /home/ubuntu/aeval/bench_horn/{1}.smt2 &> /home/ubuntu/out/std.log ; " \
  "cd /home/ubuntu ; " \
  "tar -zcf out-{1}-{2}-i{3}.tar.gz out/ ;" \
  ::: 2,agg_on 2,agg_off 5,agg_on 5,agg_off ::: {0..9}

# Remove the disabling of StrictHostKeyChecking
mv ~/.ssh/config.backup ~/.ssh/config
