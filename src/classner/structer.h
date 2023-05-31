#ifndef STRUCTER_H
#define STRUCTER_H

#include <QFile>
#include <QString>
#include <iostream>
#include <QTextStream>
#include <bits/stdc++.h>

#include "specialvals.h"

using namespace std;

class Structer
{
private:
  map<QString, QStringList> _structs;
public:
  Structer() {}
  void readStructs(QString filePath);
  map<QString, QStringList> getStructs() {return _structs;}
};

#endif // STRUCTER_H
