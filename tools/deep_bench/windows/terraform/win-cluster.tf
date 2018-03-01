variable "cluster_size" {
  default = "5"
}

variable "win_admin_pwd" {
  default = "windowsisfun400!"
}

variable "instance_type" {
  default = "m4.xlarge"
}

variable "freqhorn_windows_ami" {
  default = ""
}

provider "aws" {}

data "http" "ip" {
  url = "http://icanhazip.com"
}

#
# Simple VPC for instance
#
resource "aws_vpc" "main" {
  cidr_block = "192.168.0.0/16"

  tags {
    Name = "BenchmarkFreqHorn-Windows-VPC"
  }
}

resource "aws_subnet" "main" {
  vpc_id                  = "${aws_vpc.main.id}"
  cidr_block              = "192.168.1.0/24"
  map_public_ip_on_launch = true

  tags {
    Name = "BenchmarkFreqHorn-Windows-Subnet"
  }
}

resource "aws_internet_gateway" "igw" {
  vpc_id = "${aws_vpc.main.id}"

  tags {
    Name = "BenchmarkFreqHorn-Windows-InternetGateway"
  }
}

resource "aws_route" "igw_route" {
  route_table_id         = "${aws_vpc.main.main_route_table_id}"
  destination_cidr_block = "0.0.0.0/0"
  gateway_id             = "${aws_internet_gateway.igw.id}"
}

resource "aws_security_group" "secgrp" {
  name        = "BenchmarkFreqHorn-Windows-SecGrp"
  description = "Allow inbound SSH"
  vpc_id      = "${aws_vpc.main.id}"

  # SSH from local IP
  ingress {
    from_port = 22
    to_port   = 22
    protocol  = "tcp"

    cidr_blocks = [
      "${chomp(data.http.ip.body)}/32",
    ]
  }

  # WinRM from local IP
  ingress {
    from_port = 5985
    to_port   = 5986
    protocol  = "tcp"

    cidr_blocks = [
      "${chomp(data.http.ip.body)}/32",
    ]
  }

  # RDP from local IP
  ingress {
    from_port = 3389
    to_port   = 3389
    protocol  = "tcp"

    cidr_blocks = [
      "${chomp(data.http.ip.body)}/32",
    ]
  }

  # All outbound is fine
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
  name = "BenchmarkFreqHorn-Windows-IAMSpotFleetRole"

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
  name = "BenchmarkFreqHorn-Windows-IAMSpotFleetRolePolicy"
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
# Default AMI
#

data "aws_ami" "windows2012" {
  most_recent = true
  owners      = ["amazon"]

  filter {
    name   = "name"
    values = ["Windows_Server-2012-R2_RTM-English-64Bit-Base-*"]
  }
}

#
# Instances
#

data "template_file" "init" {
  template = "${file("userdata.tpl")}"

  vars {
    win_admin_pwd = "${var.win_admin_pwd}"
  }
}

resource "aws_spot_fleet_request" "fleet_req" {
  iam_fleet_role = "${aws_iam_role.iam_fleet_role.arn}"

  spot_price                          = "0.3"
  target_capacity                     = "${var.cluster_size}"
  terminate_instances_with_expiration = true

  launch_specification {
    instance_type               = "${var.instance_type}"
    ami                         = "${var.freqhorn_windows_ami != "" ? var.freqhorn_windows_ami : data.aws_ami.windows2012.id}"
    subnet_id                   = "${aws_subnet.main.id}"
    vpc_security_group_ids      = ["${aws_security_group.secgrp.id}"]
    associate_public_ip_address = true
    user_data                   = "${data.template_file.init.rendered}"

    # non-dedicated because m4.xlarge doesn't supported that tenancy mode
    # placement_tenancy = "dedicated"

    root_block_device {
      volume_size = "40"
      volume_type = "gp2"
    }

    tags {
      Project = "FreqHorn"
      FreqHornPlatform = "Windows"
    }
  }
}
