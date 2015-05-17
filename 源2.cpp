// 圈地为王游戏样例程序
// Enclosure Sample 
// 最后更新 2013-06-25 21:56
// 作者：zhouhy

// AI添加
// AI Extension
// Author: Ruogu Du

#include <iostream>
#include <string>
#include <ctime>
#include <set>
#include <vector>
/***************以下是新加入内容***************/
#include <cmath>
#include <memory.h>
/***************以上是新加入内容***************/
#include <algorithm>

#define INITIAL_OWNER -1 // 无主
#define TEMPORARY_FLAG -2 // 临时标志
#define max(a, b) ((b < a) ? (a) : (b))
#define min(a, b) ((a < b) ? (a) : (b))
#define PLAYER_COUNT  4
#define FIELD_WIDTH 10
#define FIELD_HEIGHT 10
/***************以下是新加入内容***************/
#define RESTING_STATE 0
#define DRAWING_STATE 1
#define SKILL_USING_STATE -1
#define ATTACK_DISTANCE 40
#define MAX_VALUE 999999999
#define SAFE_DISTANCE 20
#define DANGEROUS_DISTANCE 4
/***************以上是新加入内容***************/
using namespace std;

struct Point
{
	int x, y;
	Point(int _x, int _y) : x(_x), y(_y) { }

	Point()
	{
		x = y = 0;
	}

	bool operator<(const Point& b) const
	{
		if (y == b.y)
			return x < b.x;
		return y < b.y;
	}

	bool operator==(const Point& b) const
	{
		return x == b.x && y == b.y;
	}

	bool operator!=(const Point& b) const
	{
		return !operator==(b);
	}

	void operator+=(const Point& b)
	{
		x += b.x;
		y += b.y;
	}
};
/***************以下是新加入内容***************/
inline int calcDistance(const Point &p1, const Point &p2)
{
	return abs(p1.x - p2.x) + abs(p1.y - p2.y);
}
inline int d_calcDistance(Point &p1, Point &p2)
{
	return (p1.x - p2.x) * (p1.x - p2.x) + (p1.y - p2.y) * (p1.y - p2.y);
}
/***************以上是新加入内容***************/
int playerLeft, myID, turnCount, vborders[FIELD_WIDTH + 1][FIELD_HEIGHT], hborders[FIELD_WIDTH][FIELD_HEIGHT + 1], //记录轨迹用
	vborderOwner[FIELD_WIDTH + 1][FIELD_HEIGHT], hborderOwner[FIELD_WIDTH][FIELD_HEIGHT + 1], // 记录可否行走用
	grids[FIELD_WIDTH][FIELD_HEIGHT], areaSquareSum[PLAYER_COUNT], areaSum[PLAYER_COUNT], // 记录格子占领情况
	dx[5] = {0, 0, -1, 1, 0}, dy[5] = {-1, 1, 0, 0, 0}, playerState[PLAYER_COUNT], // 0为抬笔，1为落笔，-1为死亡
	stuckStatusLeft[PLAYER_COUNT], // 玩家被束缚剩余回合数
	scoreDecline[PLAYER_COUNT]; // 玩家因施放技能损失的分数
char actions[5] = {'u', 'd', 'l', 'r', 's'},
	lastDir[PLAYER_COUNT]; // 上次走的方向，仅用于落笔后状态
Point prevPos[PLAYER_COUNT], currPos[PLAYER_COUNT];
vector<Point> trail[PLAYER_COUNT];
set<Point> traps;
/***************以下是新加入内容***************/
int t_vborders[FIELD_WIDTH + 1][FIELD_HEIGHT], t_hborders[FIELD_WIDTH][FIELD_HEIGHT + 1];
void h_boardCopy(int dst[FIELD_WIDTH][FIELD_HEIGHT + 1], int src[FIELD_WIDTH][FIELD_HEIGHT + 1])
{
	for(int i = 0; i < FIELD_WIDTH; i++)
		for(int j = 0; j < FIELD_HEIGHT + 1; j++)
		{
			dst[i][j] = src[i][j];
			src[i][j] = -1;
		}
}
void v_boardCopy(int dst[FIELD_WIDTH + 1][FIELD_HEIGHT], int src[FIELD_WIDTH + 1][FIELD_HEIGHT])
{
	for(int i = 0; i < FIELD_WIDTH + 1; i++)
		for(int j = 0; j < FIELD_HEIGHT; j++)
		{
			dst[i][j] = src[i][j];
			src[i][j] = -1;
		}
}
/***************以上是新加入内容***************/
struct EnclosingArgu
{
	int enclosedArea,  // 被圈住的内部面积，包括不可占据区域
		charID;
	set<Point> actuallyOccupiedArea; // 实际属于该角色的网格坐标
	bool willBeDead[PLAYER_COUNT];
	bool operator<(const EnclosingArgu& b) const
	{
		return enclosedArea < b.enclosedArea;
	}
};

inline void DrawLine(int charID, Point& prevPos, Point& currPos)
{
	if (currPos == prevPos)
		return;
	if (currPos.x == prevPos.x)
		vborders[currPos.x][min(prevPos.y, currPos.y)] = charID;
	else if (currPos.y == prevPos.y)
		hborders[min(prevPos.x, currPos.x)][currPos.y] = charID;
}
/************************************/
inline void CleanLine(int charID, Point& prevPos, Point& currPos)
{
	if (currPos == prevPos)
		return;
	if (currPos.x == prevPos.x)
		vborders[currPos.x][min(prevPos.y, currPos.y)] = INITIAL_OWNER;
	else if (currPos.y == prevPos.y)
		hborders[min(prevPos.x, currPos.x)][currPos.y] = INITIAL_OWNER;
}
/************************************/
inline bool MoveStep(int &x, int &y, int dir, int charID) // 移动并检查是否撞到charID边界
{
	if (dir == 0)
	{
		if (hborders[x][y] == charID)
			return false;
	}
	else if (dir == 1)
	{
		if (hborders[x][y + 1] == charID)
			return false;
	}
	else if (dir == 2)
	{
		if (vborders[x][y] == charID)
			return false;
	}
	else if (dir == 3)
	{
		if (vborders[x + 1][y] == charID)
			return false;
	}
	x += dx[dir];
	y += dy[dir];
	if (x < 0 || x >= FIELD_WIDTH || y < 0 || y >= FIELD_HEIGHT)
		return false;
	return true;
}

inline bool MoveStep(int &x, int &y, int dir) // 移动
{
	x += dx[dir];
	y += dy[dir];
	if (x < 0 || x >= FIELD_WIDTH || y < 0 || y >= FIELD_HEIGHT)
		return false;
	return true;
}

int TryExpand(int charID, 
			  int tempBoard[FIELD_WIDTH][FIELD_HEIGHT], 
			  int gridX, int gridY,
			  set<Point>& actuallyOccupiedArea, 
			  bool willBeDead[PLAYER_COUNT]) // 试图用漫水法找出charID所围全部区域
{
	if (tempBoard[gridX][gridY] == TEMPORARY_FLAG) // tempBoard复制grids，但增加了TEMPORARY_FLAG这种状态，表示已经走过
		return 0;
	int x, y, area = 0, initialOwner = tempBoard[gridX][gridY]; // area为所围区域全部面积
	tempBoard[gridX][gridY] = TEMPORARY_FLAG;
	for (int dir = 0; dir < 4; dir++)
	{
		x = gridX;
		y = gridY;
		if (MoveStep(x, y, dir, charID))
			area += TryExpand(charID, tempBoard, x, y, actuallyOccupiedArea, willBeDead);
	}
	if (gridX > 0 && gridX < FIELD_WIDTH && gridY > 0 && gridY < FIELD_HEIGHT &&
		hborders[gridX - 1][gridY] != charID && hborders[gridX][gridY] != charID &&
		vborders[gridX][gridY - 1] != charID && vborders[gridX][gridY] != charID)
	{
		for (int i = 0; i < PLAYER_COUNT; i++)
			if (prevPos[i].x == gridX && prevPos[i].y == gridY)
				willBeDead[i] = true;
	}
	if (initialOwner == INITIAL_OWNER)
		actuallyOccupiedArea.insert(Point(gridX, gridY));
	return area + 1;
}

int TryExpand(int tempBoard[FIELD_WIDTH][FIELD_HEIGHT], int gridX, int gridY, set<Point>& allArea) // 试图用漫水法从gridX/Y开始找出内容为TEMPFLAG的连续格子面积
{
	if (tempBoard[gridX][gridY] != TEMPORARY_FLAG)
		return 0;
	int x, y, area = 0; // area为所围区域全部面积
	tempBoard[gridX][gridY] = INITIAL_OWNER;
	allArea.insert(Point(gridX, gridY));
	for (int dir = 0; dir < 4; dir++)
	{
		x = gridX;
		y = gridY;
		if (MoveStep(x, y, dir))
			area += TryExpand(tempBoard, x, y, allArea);
	}
	return area + 1;
}


// 产生圈地的参数，因为根据规则，在正式圈地之前还要从小到大排序
EnclosingArgu CalcEnclose(int charID, vector<Point>::iterator p, vector<Point>::iterator e) // p~e是真正在边界上的点
{
	EnclosingArgu tempArgu;
	for (int i = 0; i < PLAYER_COUNT; i++)
		tempArgu.willBeDead[i] = false;

	// 从最高的横线向下漫水搜索
	sort(p, e);
	vector<Point>::iterator lp = p;
	for (++p; p != e; ++p, ++lp)
		if (p->x - lp->x == 1)
			break;

	int tempGrids[FIELD_WIDTH][FIELD_HEIGHT];
	for (int x = 0; x < FIELD_WIDTH; x++)
		for (int y = 0; y < FIELD_HEIGHT; y++)
			tempGrids[x][y] = grids[x][y];

	tempArgu.enclosedArea = TryExpand(charID, tempGrids, lp->x, lp->y, tempArgu.actuallyOccupiedArea, tempArgu.willBeDead);
	tempArgu.charID = charID;
	return tempArgu;
}

// 按照圈地参数进行正式圈地
void DoEnclose(const EnclosingArgu& argu)
{
	int currArea;
	int tempGrids[FIELD_WIDTH][FIELD_HEIGHT]; // 用于找出连续区域
	for (int x = 0; x < FIELD_WIDTH; x++)
		for (int y = 0; y < FIELD_HEIGHT; y++)
			tempGrids[x][y] = INITIAL_OWNER;

	for (int i = 0; i < PLAYER_COUNT; i++)
		if (argu.willBeDead[i])
			playerState[i] = -1;

	set<Point>::const_iterator i, e;
	for (i = argu.actuallyOccupiedArea.begin(), e = argu.actuallyOccupiedArea.end(); i != e; i++)
	{
		grids[i->x][i->y] = argu.charID;
		tempGrids[i->x][i->y] = TEMPORARY_FLAG;
	}

	// 标记所有内部边
	Point x1, x2;
	for (x1.x = 0; x1.x < FIELD_WIDTH; x1.x++)
		for (x1.y = 0; x1.y < FIELD_HEIGHT; x1.y++)
		{
			if (x1.x < FIELD_WIDTH - 1)
			{
				x2.x = x1.x + 1;
				x2.y = x1.y;
				if (tempGrids[x1.x][x1.y] == TEMPORARY_FLAG && tempGrids[x2.x][x2.y] == TEMPORARY_FLAG &&
					argu.actuallyOccupiedArea.count(x1) && argu.actuallyOccupiedArea.count(x2))
					vborderOwner[x2.x][x2.y] = argu.charID;
			}
			if (x1.y < FIELD_HEIGHT - 1)
			{
				x2.x = x1.x;
				x2.y = x1.y + 1;
				if (tempGrids[x1.x][x1.y] == TEMPORARY_FLAG && tempGrids[x2.x][x2.y] == TEMPORARY_FLAG &&
					argu.actuallyOccupiedArea.count(x1) && argu.actuallyOccupiedArea.count(x2))
					hborderOwner[x2.x][x2.y] = argu.charID;
			}
		};

	areaSum[argu.charID] += argu.actuallyOccupiedArea.size();
	set<Point> allArea;

	// 找出所有连续的区域
	for (i = argu.actuallyOccupiedArea.begin(); i != e; i++)
		if (tempGrids[i->x][i->y] == TEMPORARY_FLAG)
		{
			allArea.clear();
			currArea = TryExpand(tempGrids, i->x, i->y, allArea);
			areaSquareSum[argu.charID] += currArea * currArea;
		};

	// 清除轨迹
	int x, y;
	for (x = 0; x <= FIELD_WIDTH; x++)
		for (y = 0; y <= FIELD_HEIGHT; y++)
		{
			if (x < FIELD_WIDTH && hborders[x][y] == argu.charID)
				hborders[x][y] = INITIAL_OWNER;
			if (y < FIELD_HEIGHT && vborders[x][y] == argu.charID)
				vborders[x][y] = INITIAL_OWNER;
		};
	trail[argu.charID].clear();
}

bool CheckRoute(int charID, int state, Point& prevPos, Point& currPos) // 检查路线是否可以行走
{
	if (currPos == prevPos)
		return true;
	if (currPos.y == prevPos.y)
		if (currPos.y == 0 || currPos.y == FIELD_HEIGHT)
			return true;
		else
		{
			int gridX = currPos.x;
			if (prevPos.x < gridX)
				gridX = prevPos.x;
			if ((state == 1 && hborderOwner[gridX][currPos.y] != INITIAL_OWNER) ||
				(state == 0 && hborderOwner[gridX][currPos.y] != INITIAL_OWNER && hborderOwner[gridX][currPos.y] != charID))
				return false;
			return true;
		}
	else
		if (currPos.x == 0 || currPos.x == FIELD_WIDTH)
			return true;
		else
		{
			int gridY = currPos.y;
			if (prevPos.y < gridY)
				gridY = prevPos.y;
			if ((state == 1 && vborderOwner[currPos.x][gridY] != INITIAL_OWNER) ||
				(state == 0 && vborderOwner[currPos.x][gridY] != INITIAL_OWNER && vborderOwner[currPos.x][gridY] != charID))
				return false;
			return true;
		}
}

inline bool CheckPosValidity(Point& pos)
{
	if (pos.x >= 0 && pos.x <= FIELD_WIDTH &&
		pos.y >= 0 && pos.y <= FIELD_HEIGHT)
		return true;
	return false;
}

inline bool IsReverse(int dir1, int dir2) // 判断方向是否相反
{
	if (dir1 == 0 && dir2 == 1)
		return true;
	if (dir1 == 1 && dir2 == 0)
		return true;
	if (dir1 == 2 && dir2 == 3)
		return true;
	if (dir1 == 3 && dir2 == 2)
		return true;
	return false;
}

inline int GetDistance(int ida, int idb) // 获得两名角色之间的坐标差
{
	int deltax = currPos[ida].x - currPos[idb].x, deltay = currPos[ida].y - currPos[idb].y;
	if (deltax < 0)
		deltax *= -1;
	if (deltay < 0)
		deltay *= -1;
	return deltax + deltay;
}
/***************以下是新加入内容***************/
int generateRandomPosition(int changePenState, int playerState)
{
	int i;
	Point temp;
	while (true)
	{
		i = rand() % (changePenState == SKILL_USING_STATE ? 4 : 5);
		if(i == 4) // 我不要不动！
			continue;
		temp.x = currPos[myID].x + dx[i];
		temp.y = currPos[myID].y + dy[i];
		if (CheckPosValidity(temp) && CheckRoute(myID, playerState, currPos[myID], temp))
		{
			if(playerState == DRAWING_STATE && !IsReverse(i, lastDir[myID]) )
				break;
			else if(playerState != DRAWING_STATE)
				break;
		}
	};
	return i;
}
int generatePosition(int changePenState, int playerState)
{
	int i = 0;
	Point temp;
	while (i < 4)
	{
		temp.x = currPos[myID].x + dx[i];
		temp.y = currPos[myID].y + dy[i];
		if (CheckPosValidity(temp) && CheckRoute(myID, playerState, currPos[myID], temp))
		{
			if(playerState == DRAWING_STATE && !IsReverse(i, lastDir[myID]) )
				break;
			else if(playerState != DRAWING_STATE)
				break;
		}
		i++;
	}
	return i;
}
void attackDecision(int player, bool &attackStatus, Point &destPoint, int &miniDistance, int &attackPlayer)
{
	if(playerState[player] != DRAWING_STATE)
		return;
	vector<Point>::iterator first = trail[player].begin();
	vector<Point>::iterator last = trail[player].end();
	int rescueDistance = calcDistance(*first, currPos[player]),
		temp;
	while(first != last)
	{
		temp = calcDistance(*first, currPos[player]);
		rescueDistance = rescueDistance <= temp? rescueDistance : temp;
		temp = calcDistance(*first, currPos[myID]);
		if(temp - rescueDistance < miniDistance - 1) // 可以攻击 // 主要修改这里
		{
			attackStatus = true;
			destPoint = *first;
			miniDistance = temp - rescueDistance;
			attackPlayer = player;
		}
		first++;
	}
}

int doAttack(int player, int changePenState, Point destPoint, bool &attackStatus, int &miniDistance)
{
	if(playerState[player] != DRAWING_STATE)
	{
		attackStatus = false;
		return generateRandomPosition(changePenState, RESTING_STATE);
	}
	int i = 0, minii = 0, miniDis = MAX_VALUE ;
	Point temp;
	while (i < 5 - (changePenState == SKILL_USING_STATE) )
	{
		temp.x = currPos[myID].x + dx[i];
		temp.y = currPos[myID].y + dy[i];
		if (CheckPosValidity(temp) 
			&& CheckRoute(myID, changePenState, currPos[myID], temp) )
		{
			if(calcDistance(destPoint, temp) < miniDis)
			{
				miniDis = calcDistance(destPoint, temp);
				minii = i;
			}
		}
		i++;
	};
	i = minii;
	if(miniDis == MAX_VALUE) // 没有找到合适的位置
	{
		attackStatus = false;
		i = generateRandomPosition(changePenState, RESTING_STATE);
	}
	return i;
}

int attackingMode(int &miniDistance, bool &attackStatus, Point &destPoint, int &attackPlayer, int &changePenState)
{
	int i;
	miniDistance = ATTACK_DISTANCE;
	attackStatus = false;
	for(i = 0; i < PLAYER_COUNT; i++)
		attackDecision(i, attackStatus, destPoint, miniDistance, attackPlayer);
	if(attackStatus) // 找到攻击对象
	{
		i = doAttack(attackPlayer, changePenState, destPoint, attackStatus, miniDistance);
	}
	else // 没找到攻击对象
	{
		i = generateRandomPosition(changePenState, changePenState);
	}
	return i;
}

int calcValidPosition(int changePenState)
{
	int i = 0;
	Point temp;
	int Count = 0;
	while (i < 4)
	{
		temp.x = currPos[myID].x + dx[i];
		temp.y = currPos[myID].y + dy[i];
		if (CheckPosValidity(temp)
			&& CheckRoute(myID, changePenState, currPos[myID], temp))
		{
			Count++;
		}
		i++;
	}
	return Count;
}
bool checkNextStep(int tempi, Point &stablePoint)
{
	int i = 0;
	Point temp;
	int d_miniDis = MAX_VALUE;
	int d_miniDis2 = MAX_VALUE;
	int d_miniDis3 = MAX_VALUE;
	bool tb;
	int minii = -1, minij = -1, minik = -1;
	while (i < 4)
	{
		temp.x = currPos[myID].x + dx[i] + dx[tempi];
		temp.y = currPos[myID].y + dy[i] + dy[tempi];
		if (!IsReverse(i, lastDir[myID]))
		{
			if(tb = (find(trail[myID].begin(), trail[myID].end(), temp) == trail[myID].end()))
			{
				if(d_calcDistance(stablePoint, temp) < d_miniDis)
				{
					d_miniDis = d_calcDistance(stablePoint, temp);
					minii = i;
				}
			}
			if (CheckPosValidity(temp)
				&& CheckRoute(myID, DRAWING_STATE, currPos[myID], temp)) // 符合一般条件
			{
				if (tb) // 不会close
				{
					if (d_miniDis2 > d_calcDistance(stablePoint, temp))
					{
						d_miniDis2 = d_calcDistance(stablePoint, temp);
						minij = i;
					}
				}
				// 可能会close
				if (d_miniDis3 > d_calcDistance(stablePoint, temp))
				{
					d_miniDis3 = d_calcDistance(stablePoint, temp);
					minik = i;
				}
			}
		}
		i++;
	};
	if(minii != minij) 
	{
		if(d_miniDis3 > d_miniDis)
			return false;
	}
	return true;
}
int circlingMode(bool circlingStatus, int &changePenState, Point &stablePoint)
{
	int miniDis = MAX_VALUE;
	circlingStatus = false; // 调试
	if(circlingStatus == false)
	{
		if(calcDistance(stablePoint, currPos[myID]) > SAFE_DISTANCE)
			circlingStatus = true;
		else
		{
			for(int i = 0; i < PLAYER_COUNT; i++)
			{
				if (i == myID || playerState[i] == -1)
					continue;
				vector<Point>::iterator ite = trail[myID].begin();
				while(ite != trail[myID].end())
				{
					if(calcDistance(currPos[i], *ite) < miniDis)
					{
						miniDis = calcDistance(currPos[i], *ite);
					}
					ite++;
				}
			}
			if(miniDis < DANGEROUS_DISTANCE) // 这里有问题
				circlingStatus = true;
		}
	}
	if(circlingStatus == false)
	{
		int minii = -1;
		int d_miniDis = MAX_VALUE;
		int minij = -1;
		int d_miniDis2 = MAX_VALUE;
		int minik = -1;
		int d_miniDis3 = MAX_VALUE;
		bool tb;
		Point temp;
		int i = 0;
		while (i < 4)
		{
			temp.x = currPos[myID].x + dx[i];
			temp.y = currPos[myID].y + dy[i];
			if (!IsReverse(i, lastDir[myID]))
			{
				if(tb = (find(trail[myID].begin(), trail[myID].end(), temp) == trail[myID].end()))
				{
					if(d_calcDistance(stablePoint, temp) < d_miniDis)
					{
						d_miniDis = d_calcDistance(stablePoint, temp);
						minii = i;
					}
				}
				if (CheckPosValidity(temp)
					&& CheckRoute(myID, DRAWING_STATE, currPos[myID], temp)) // 符合一般条件
				{
					if (tb) // 不会close
					{
						if (d_miniDis2 > d_calcDistance(stablePoint, temp))
						{
							d_miniDis2 = d_calcDistance(stablePoint, temp);
							minij = i;
						}
					}
					// 可能会close
					if (d_miniDis3 > d_calcDistance(stablePoint, temp))
					{
						d_miniDis3 = d_calcDistance(stablePoint, temp);
						minik = i;
					}
				}
			}
			i++;
		};
		if (trail[myID].empty())
			i = minij;
		else if(minii == minij)
		{
			if(checkNextStep(minij, stablePoint))
				i = minij;
			else
				i = minik;
		}
		else
		{
			i = minik;
		}
		return i;
	}
	else
	{
		int minii = -1;
		int d_miniDis = MAX_VALUE;
		Point safePoint;
		Point temp;
		int i = 0;
		while (i < 4 )
		{
			temp.x = currPos[myID].x + dx[i];
			temp.y = currPos[myID].y + dy[i];
			if (CheckPosValidity(temp) 
				&& CheckRoute(myID, DRAWING_STATE, currPos[myID], temp)
				&& !IsReverse(i, lastDir[myID]))
			{
				vector<Point>::iterator ite = trail[myID].begin();
				while(ite != trail[myID].end())
				{
					if(*ite != currPos[myID])
					{
						if(d_calcDistance(temp, *ite) < d_miniDis)
						{
							d_miniDis = d_calcDistance(temp, *ite);
							safePoint = *ite; // 好像没什么用
							minii = i;
						}
					}
					ite++;
				}
			}
			i++;
		};
		i = minii;
		return i;
	}

}

int Besti = -1;
int maxArea = 0;
int maxStep = 3;
int Secondi = -1;
int miniDis;
int miniPlayerDis[4];
//int lastMove;
bool allertSign;
bool headSign;
int SafetyDistance;
int SafetyMaxArea;
int BestStepNum;
bool findPo = false;
int headDis = MAX_VALUE;
vector<Point> searchTrail;
void searchBestStep(int firstStep, int lastStep, Point lastPoint, int stepNum)
{
	if(stepNum == 0)
	{
		headDis = MAX_VALUE;
		miniDis = 8; // 可以设定
		searchTrail = trail[myID];
		if(searchTrail.empty())
			searchTrail.push_back(lastPoint);
		for(int i = 0; i < PLAYER_COUNT; i++)
		{
			if (i == myID || playerState[i] == -1)
				continue;
			if(GetDistance(myID, i) < headDis) // 头碰头距离
				headDis = GetDistance(myID, i);
			vector<Point>::iterator ite = searchTrail.begin();
			while(ite != searchTrail.end())
			{
				if(calcDistance(currPos[i], *ite) < miniDis)
				{
					miniDis = calcDistance(currPos[i], *ite);
				}
				ite++;
			}
		}
		maxStep = miniDis;
//		maxStep = miniDis - 1;
		int playerDis = MAX_VALUE;
		for(int i = 0; i < 4; i++)
		{
			playerDis = MAX_VALUE;
			Point tPo(currPos[myID].x+dx[i], currPos[myID].y+dy[i]);
			for(int p = 0; p < PLAYER_COUNT; p++)
			{
				if (p == myID || playerState[p] == -1)
					continue;
				if(calcDistance(tPo, currPos[p]) < playerDis) // 头碰头距离
					playerDis = calcDistance(tPo, currPos[p]);
			}
			miniPlayerDis[i] = playerDis;
		}
		if(headDis == maxStep && maxStep <= 6) // 避免头碰头
			headSign = true;
		else
			headSign = false;
		maxArea = 0;
		Besti = -1;
		Secondi = -1;
		SafetyDistance = MAX_VALUE;
		SafetyMaxArea = 0;
		if(maxStep <= 3 || headDis <= 4) // 危险了
		{
//			maxStep = 5;
//			allertSign = true;
			allertSign = false;
		}
		else
			allertSign = false;
	}
	if(stepNum > maxStep) 
	{
		if(maxStep < 2)
		{
			if(stepNum > maxStep + 5)
				return;
		}
		else if((maxStep < 3 && stepNum > maxStep + 4)
				|| (maxStep >= 3 && maxStep <= 5 && stepNum > maxStep + 1))
				return;
		else if(stepNum > 7)
			return;
	}
	if(stepNum != 0)
	{
		vector<Point>::iterator it;
		int mSize = searchTrail.size();
		it = find(searchTrail.begin(), searchTrail.end(), lastPoint);
		if (it != searchTrail.end() && it != --searchTrail.end())
		{
			if(miniPlayerDis[firstStep] <= 1 && stepNum > 1)
				return;
			if(allertSign == false)
			{
				v_boardCopy(t_vborders, vborders);
				h_boardCopy(t_hborders, hborders);
				vector<Point> tempVec;
				while(it != searchTrail.end())
				{
					tempVec.push_back(*it);
					it++;
				}
				vector<Point>::iterator ite = tempVec.begin()+1;
				while(ite != tempVec.end())
				{
					DrawLine(myID, *(ite-1), *ite);
					ite++;
				}
				DrawLine(myID, *(ite-1), *tempVec.begin());
				EnclosingArgu eArgu = CalcEnclose(myID, tempVec.begin(), tempVec.end());
				int OccupiedArea = eArgu.actuallyOccupiedArea.size();
				v_boardCopy(vborders, t_vborders);
				h_boardCopy(hborders, t_hborders);
				if(stepNum <= maxStep - headSign) // 特殊情况
				{
					if(OccupiedArea > maxArea)
					{
						Besti = firstStep;
						BestStepNum = stepNum;
						maxArea = OccupiedArea;
					}
					else if(OccupiedArea == maxArea && maxArea != 0)
					{
						if(BestStepNum > stepNum)
						{
							Besti = firstStep;
							BestStepNum = stepNum;
						}
						else if(BestStepNum == stepNum)
						{
							if(miniPlayerDis[firstStep] > miniPlayerDis[Besti])
							{
								Besti = firstStep;
							//	BestStepNum = stepNum;
							}
						}
					}
				}
				else
				{
					if(stepNum == maxStep && headDis < miniPlayerDis[firstStep] && OccupiedArea > maxArea)
					{
						Besti = firstStep;
						BestStepNum = stepNum;
						maxArea = OccupiedArea;
					}
					if(stepNum < SafetyDistance)
					{
						Secondi = firstStep;
						SafetyDistance = stepNum;
						if(OccupiedArea > SafetyMaxArea)
							SafetyMaxArea = OccupiedArea;
					}
					else if(stepNum == SafetyDistance)
					{
						if(OccupiedArea > SafetyMaxArea)
						{
							SafetyMaxArea = OccupiedArea;
							Secondi = firstStep;
						}
						else if(calcDistance(*searchTrail.begin(), Point(currPos[myID].x+dx[firstStep],currPos[myID].y+dy[firstStep]))
							< calcDistance(*searchTrail.begin(), currPos[myID]))
						{
							SafetyMaxArea = OccupiedArea;
							Secondi = firstStep;
						}
					}
				}
			}
			else
			{
				if(stepNum <= SafetyDistance)
				{
					v_boardCopy(t_vborders, vborders);
					h_boardCopy(t_hborders, hborders);
					vector<Point> tempVec;
					while(it != searchTrail.end())
					{
						tempVec.push_back(*it);
						it++;
					}
					vector<Point>::iterator ite = tempVec.begin()+1;
					while(ite != tempVec.end())
					{
						DrawLine(myID, *(ite-1), *ite);
						ite++;
					}
					DrawLine(myID, *(ite-1), *tempVec.begin());
					EnclosingArgu eArgu = CalcEnclose(myID, tempVec.begin(), tempVec.end());
					int OccupiedArea = eArgu.actuallyOccupiedArea.size();
					v_boardCopy(vborders, t_vborders);
					h_boardCopy(hborders, t_hborders);
					if(stepNum < SafetyDistance)
					{
						Besti = firstStep;
						SafetyDistance = stepNum;
						if(OccupiedArea > maxArea)
							maxArea = OccupiedArea;
					}
					else
					{
						if(OccupiedArea > maxArea)
						{
							Besti = firstStep;
							maxArea = OccupiedArea;
						}
					}
				}
			}
			return;
		}
		searchTrail.push_back(lastPoint); // 插入trail
	}
	int i = 0;
	Point temp;
	while(i < 4)
	{
		temp.x = lastPoint.x + dx[i];
		temp.y = lastPoint.y + dy[i];
		if (CheckPosValidity(temp) 
			&& CheckRoute(myID, DRAWING_STATE, lastPoint, temp)
			&& !IsReverse(i, lastStep))
		{
			if(stepNum == 0) // 第一次
				searchBestStep(i, i, temp, stepNum+1);
			else
				searchBestStep(firstStep, i, temp, stepNum+1);
		}
		i++;
	}
	if(stepNum != 0)
		searchTrail.pop_back(); // 弹出trail
}
/***************以上是新加入内容***************/
double judgearea(int tempx, int tempy)
{
	double ans = 0;
	for(int i = 0; i < FIELD_WIDTH; i++)
		for(int j = 0; j < FIELD_HEIGHT; j++) // 有修改
		{
			if(grids[i][j] == INITIAL_OWNER && (i != tempx && j != tempy))
				ans -= 7.0 / ((i-tempx) * (i - tempx) + (j - tempy) * (j - tempy) + 2); 
			else
				ans += 1.0 / ((i-tempx) * (i - tempx) + (j - tempy) * (j - tempy) + 0.5); 
		}
	if(grids[tempx][tempy] == INITIAL_OWNER) // 倾向于选择空白格子
		ans -= 2;
	for(int i = 0; i < 4; i++)
	{
		if(playerState[i] != -1)
		{
			if(i != myID)  
				ans += 60.0 / ((currPos[i].x - tempx) * (currPos[i].x - tempx ) + (currPos[i].y - tempy) * (currPos[i].y - tempy) + 2);
			else
				ans += 40.0 / ((currPos[i].x - tempx) * (currPos[i].x - tempx ) + (currPos[i].y - tempy) * (currPos[i].y - tempy) + 2);
		}
	}
	return ans;
}

double judgeAverage;
bool judgeSign = false;
double judgeChart[10][10];
int tempi;
int judgePosition()
{
	Point temp;
	int i = -1;
	double minans = 10000000.0;
	int tempx,tempy;
	judgeAverage = 0;
	for(int row = 0; row < 10; row++)
		for(int col = 0; col < 10; col++)
		{
			double temp = judgearea(row,col);
			judgeChart[row][col] = temp; // 测试用表
			judgeAverage += temp;
			if(temp < minans)
			{
				tempx = row;
				tempy = col;
				minans = temp;
			}
		}
	judgeAverage /= 100;
	double dis = 1000000.0;
	for(int j = 0; j < 4; j++)
	{
		temp.x = currPos[myID].x + dx[j];
		temp.y = currPos[myID].y + dy[j];
		if (CheckPosValidity(temp) && CheckRoute(myID, 0, currPos[myID], temp))
		{
			Point t(tempx,tempy); 
			double a = calcDistance(temp,t);
			if(a < dis)
			{
				i = j;
				dis = a;
			}
		}
	}
	return i;
}
int main()
{
	int i, changePenState, nTraps, turnLeft;
/***************以下是新加入内容***************/
	bool attackStatus = false;
	Point destPoint;
	int miniDistance;
	int attackPlayer;
	Point stablePoint;
	bool circlingStatus = false;

	bool ifStartDraw = false;
/***************以上是新加入内容***************/
	string cmd;
	Point temp;
	multiset<EnclosingArgu> allEnclosure;
	time_t startTick;

	for (int x = 0; x <= FIELD_WIDTH; x++)
		for (int y = 0; y <= FIELD_HEIGHT; y++)
		{
			if (x != FIELD_WIDTH)
			{
				hborderOwner[x][y] = INITIAL_OWNER;
				hborders[x][y] = INITIAL_OWNER;
			}
			if (y != FIELD_HEIGHT)
			{
				vborderOwner[x][y] = INITIAL_OWNER;
				vborders[x][y] = INITIAL_OWNER;
			}
			if (x != FIELD_WIDTH && y != FIELD_HEIGHT)
				grids[x][y] = INITIAL_OWNER;
		};
	for (i = 0; i < PLAYER_COUNT; i++)
	{
		areaSquareSum[i] = areaSum[i] = 0;
		lastDir[i] = -1;
	}
	turnCount = 0;

	while (cin >> cmd)
	{
		if (cmd == "[START]")
		{
			startTick = clock();
			while (clock() - startTick < 100); // 等待0.1秒……
			srand(clock());
			cin >> myID;
//			cout << "[POS] " << rand() % (FIELD_WIDTH + 1) << ' ' << rand() % (FIELD_HEIGHT + 1) << endl;
			int rnd = rand() % 4;
			if(rnd == 0)
				cout << "[POS] " << 3 << ' ' << 3 << endl;
			else if(rnd == 1)
				cout << "[POS] " << 7 << ' ' << 3 << endl;
			else if(rnd == 2)
				cout << "[POS] " << 3 << ' ' << 7 << endl;
			else
				cout << "[POS] " << 7 << ' ' << 7 << endl;
		}
		if (cmd == "[STATUS]")
		{
			startTick = clock();
			while (clock() - startTick < 100); // 等待0.1秒……
			srand(clock());
			for (i = 0; i < PLAYER_COUNT; i++)
				cin >> currPos[i].x >> currPos[i].y >> playerState[i] >> stuckStatusLeft[i] >> scoreDecline[i];
			cin >> nTraps;
			traps.clear();
			for (i = 0; i < nTraps; i++)
			{
				cin >> temp.x >> temp.y >> turnLeft;
				traps.insert(temp);
			}

			if (++turnCount == 1) // 第一回合
				for (i = 0; i < PLAYER_COUNT; i++)
					prevPos[i] = currPos[i];
			else
			{
				for (i = 0; i < PLAYER_COUNT; i++)
				{
					vector<Point>::iterator it;
					if (playerState[i] == 0 && !trail[i].empty() && (it = find(trail[i].begin(), trail[i].end(), currPos[i])) != --trail[i].end() && it != trail[i].end())
					{
						lastDir[i] = -1;
						DrawLine(i, prevPos[i], currPos[i]);
						allEnclosure.insert(CalcEnclose(i, it, trail[i].end()));
					}
					else if (playerState[i] == 1)
					{
						if (trail[i].empty())
							trail[i].push_back(prevPos[i]);
						if (trail[i][trail[i].size() - 1] != currPos[i])
						{
							trail[i].push_back(currPos[i]);
							DrawLine(i, prevPos[i], currPos[i]);
						}
					}
				}
				for_each(allEnclosure.begin(), allEnclosure.end(), DoEnclose);
				allEnclosure.clear();
			}
			if (stuckStatusLeft[myID] > 0)
			{
				cout << "[ACTION] s 0" << endl;
				for (i = 0; i < PLAYER_COUNT; i++)
					prevPos[i] = currPos[i];
				continue;
			}

			if (playerState[myID] == RESTING_STATE)
			{
				for (i = 0; i < PLAYER_COUNT; i++)
					if (i != myID && playerState[i] != -1 && GetDistance(i, myID) < 5) // 暂时用4步法
						break;
				if (i != PLAYER_COUNT)
				{
					if (0) //KILLER
						changePenState = SKILL_USING_STATE;
					else
						changePenState = RESTING_STATE;
				}
				else if (1) // 调试
				{
//					if (calcValidPosition(DRAWING_STATE) > 2)
//					{
//						playerState[myID] = DRAWING_STATE;
//						changePenState = DRAWING_STATE;
//						circlingStatus = false; // 安全
//						stablePoint = currPos[myID];
//					}
//					else
//						changePenState = RESTING_STATE;
					playerState[myID] = DRAWING_STATE;
					changePenState = DRAWING_STATE;
					tempi = judgePosition();
					int tempx = currPos[myID].x,
						tempy = currPos[myID].y;
					if(tempx == 10)
						tempx--;
					if(tempy == 10)
						tempy--;
					if(judgeChart[tempx][tempy] <= judgeAverage + 20)
					{
						searchBestStep(-1, -1, currPos[myID], 0);
						if(Besti == -1 && miniDis <= SafetyDistance) // 设定阈值
						{
							playerState[myID] = RESTING_STATE;
							changePenState = RESTING_STATE;
							judgeSign = true;
						}
						if(Besti != -1 && maxArea < 4 && turnCount < 6)
						{
							playerState[myID] = RESTING_STATE;
							changePenState = RESTING_STATE;
							judgeSign = true;
						}
						if(Besti != -1 && BestStepNum > 4 && maxArea == 1)
						{
							playerState[myID] = RESTING_STATE;
							changePenState = RESTING_STATE;
						//	judgeSign = true;
							findPo = true;
						}
						if(Besti != -1 && BestStepNum > 6 && maxArea == 2)
						{
							playerState[myID] = RESTING_STATE;
							changePenState = RESTING_STATE;
						//	judgeSign = true;
							findPo = true;
						}
	//					lastMove = -1;
					}
					else
					{
						playerState[myID] = RESTING_STATE;
						changePenState = RESTING_STATE;
					}
				}
				else
					changePenState = RESTING_STATE;
			}
			else
				changePenState = RESTING_STATE;

			if (playerState[myID] == DRAWING_STATE) // 落笔态
			{
//				i = circlingMode(circlingStatus, changePenState, stablePoint);
//				if(trail[myID].size() <= 2)
//				{
//					do
//					{
//						i = generateRandomPosition(changePenState, playerState[myID]);
////						i = generatePosition(changePenState, playerState[myID]);
//					}while(i == lastMove);
//					lastMove = i;
//				}
//				else
//				{
					if(changePenState == RESTING_STATE)
						searchBestStep(-1, lastDir[myID], currPos[myID], 0);
					if(Besti == -1)
						Besti = Secondi;
					i = Besti;
//				}
				if (i != 4)
					lastDir[myID] = i;
			}
/***************以下是新修改内容***************/
			else
			{
				if(judgeSign)
				{
					judgeSign = false;
					i = tempi;
				}
				else if(findPo)
				{
					findPo = false;
					i = Besti;
				}
				else
				{
					i = judgePosition();
				}
/*				else 
					i = generateRandomPosition(changePenState, playerState[myID]);*/
			}
			if(changePenState == DRAWING_STATE)
				ifStartDraw = true;
/***************以上是新修改内容***************/
			cout << "[ACTION] " << actions[i] << ' ' << changePenState << endl;
			for (i = 0; i < PLAYER_COUNT; i++)
				prevPos[i] = currPos[i];
		}
	}
}
