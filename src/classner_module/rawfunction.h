#ifndef RAWFUNCTION_H
#define RAWFUNCTION_H

#include <QString>
#include <QStringList>

#include "specialvals.h"

class RawFunction
{
private:
  QString _declar;
  QString _mangledName;
  QStringList _codeLines;
public:
  RawFunction(QString declar) {_declar = declar;}
  void setMangledName(QString mangledName) {_mangledName = mangledName;}
  void addCodeLine(QString line) {_codeLines.append(line);}
  void setCodeLines(QStringList codeLines) {_codeLines = codeLines;}
  void removeCodeLine(int index) {
    if (index >= 0 && index < _codeLines.length())
      _codeLines.removeAt(index);
  }
  QString getDeclar() {return _declar;}
  QString getMangledName() {return _mangledName;}
  QString getCodeLine(int index) {return _codeLines[index];}
  QStringList getCodeLines() {return _codeLines;}
};

#endif // RAWFUNCTION_H
