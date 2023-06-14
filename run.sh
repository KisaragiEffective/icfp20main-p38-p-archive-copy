sudo docker build -t dselsam/pureptr .
sudo docker run --name PurePtr dselsam/pureptr /bin/bash
sudo docker cp PurePtr:/paper/pureptr/tower.png tower.png
sudo docker cp PurePtr:/paper/pureptr/twoTowers.png twoTowers.png
sudo docker cp PurePtr:/paper/pureptr/out/Paper.c Paper.c
sudo docker cp PurePtr:/paper/pureptr/Paper.out Paper.out
sudo docker rm PurePtr
