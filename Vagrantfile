# -*- mode: ruby -*-

VAGRANTFILE_API_VERSION = "2"

Vagrant.configure(VAGRANTFILE_API_VERSION) do |config|
  config.vm.box = "ubuntu/trusty64"
  config.vm.box_check_update = false

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 4096
    vb.cpus = 4
  end

  config.vm.provision "shell", path: "provision.sh"
end
