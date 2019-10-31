/*
 Copyright 2019 Alain Dargelas
 
 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at
 
 http://www.apache.org/licenses/LICENSE-2.0
 
 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/* 
 * File:   TimeInfo.h
 * Author: alain
 *
 * Created on June 8, 2017, 8:27 PM
 */

#ifndef TIMEINFO_H
#define TIMEINFO_H

namespace SURELOG {

class TimeInfo {
public:
    TimeInfo() : m_type(None), m_fileId(0), m_line(0), m_timeUnit(Second), m_timeUnitValue(0.0f), m_timePrecision(Second), m_timePrecisionValue(0.0f) {}
    virtual ~TimeInfo();
    typedef enum { 
        None,
        Timescale,
        TimeUnitTimePrecision        
    } Type;
    typedef enum { 
        Second,
        Millisecond,
        Microsecond,
        Nanosecond,        
        Picosecond,
        Femtosecond              
    } Unit;
    
    Type m_type;
    SymbolId m_fileId;
    unsigned int m_line;
    Unit m_timeUnit;
    double m_timeUnitValue;    
    Unit m_timePrecision;
    double m_timePrecisionValue;
    
    static Unit unitFromString(std::string s);
        
private:
    
};

};

#endif /* TIMEINFO_H */


