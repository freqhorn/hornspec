variable "cluster_size" {
  type = "int"
  default = 20
}

provider "aws" {}

#
# Simple VPC for instance
#
resource "aws_vpc" "main" {
  cidr_block = "192.168.0.0/16"

  tags {
    Name = "BenchmarkFreqHorn-VPC"
  }
}

resource "aws_subnet" "main" {
  vpc_id                  = "${aws_vpc.main.id}"
  availability_zone       = "us-east-1e"
  cidr_block              = "192.168.1.0/24"
  map_public_ip_on_launch = true

  tags {
    Name = "BenchmarkFreqHorn-Subnet"
  }
}

resource "aws_internet_gateway" "igw" {
  vpc_id = "${aws_vpc.main.id}"

  tags {
    Name = "BenchmarkFreqHorn-InternetGateway"
  }
}

resource "aws_route" "igw_route" {
  route_table_id         = "${aws_vpc.main.main_route_table_id}"
  destination_cidr_block = "0.0.0.0/0"
  gateway_id             = "${aws_internet_gateway.igw.id}"
}

resource "aws_security_group" "secgrp" {
  name        = "BenchmarkFreqHorn-SecGrp"
  description = "Allow inbound SSH"
  vpc_id      = "${aws_vpc.main.id}"

  ingress {
    from_port   = 22
    to_port     = 22
    protocol    = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

#
# Spot Fleet IAM
#
resource "aws_iam_role" "iam_fleet_role" {
  name = "BenchmarkFreqHorn-IAMSpotFleetRole"

  assume_role_policy = <<EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Effect": "Allow",
      "Principal": {
        "Service": [
          "spotfleet.amazonaws.com"
        ]
      },
      "Action": "sts:AssumeRole"
    }
  ]
}
EOF
}

resource "aws_iam_role_policy" "iam_fleet_role_policy" {
  # TODO: Restrict to read-only
  name = "BenchmarkFreqHorn-IAMSpotFleetRolePolicy"
  role = "${aws_iam_role.iam_fleet_role.name}"

  policy = <<EOF
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Effect": "Allow",
      "Action": [
        "ec2:CreateTags",
        "ec2:DescribeImages",
        "ec2:DescribeSubnet",
        "ec2:DescribeSubnets",
        "ec2:DescribeInstanceStatus",
        "ec2:DescribeSpotFleetInstances",
        "ec2:DescribeSpotFleetRequests",
        "ec2:DescribeSpotFleetRequestHistory",
        "ec2:RequestSpotFleet",
        "ec2:RequestSpotInstances",
        "ec2:CancelSpotFleetRequests",
        "ec2:TerminateInstances",
        "iam:PassRole",
        "iam:ListRoles",
        "iam:GetRole",
        "iam:ListInstanceProfiles"
      ],
      "Resource": [
        "*"
      ]
    }
  ]
}
EOF
}

#
# Find the AMI we built with ../packer/worker.json
#
data "aws_ami" "worker" {
  most_recent = true
  owners      = ["self"]

  filter {
    name   = "tag:Project"
    values = ["FreqHorn"]
  }
}

#
# Instances
#

resource "aws_spot_fleet_request" "fleet_req" {
  iam_fleet_role = "${aws_iam_role.iam_fleet_role.arn}"

  spot_price                          = "0.10"
  target_capacity                     = "${vars.cluster_size}"
  terminate_instances_with_expiration = true

  launch_specification {
    instance_type               = "m4.xlarge"
    ami                         = "${data.aws_ami.worker.id}"
    key_name                    = "deephornec2"
    subnet_id                   = "${aws_subnet.main.id}"
    vpc_security_group_ids      = ["${aws_security_group.secgrp.id}"]
    associate_public_ip_address = true

    placement_tenancy           = "dedicated"

    tags {
      Project = "FreqHorn"
    }
  }
}
