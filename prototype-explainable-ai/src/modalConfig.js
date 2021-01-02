const modalConfig = {
    "problem-type": {
        "title": "Choose a problem",
        "numButtons": 2,
        "buttonsName": [
            "Tiger",
            "Velocity Regulation"
        ],
        "next": "action-rule"
    },
    "action-rule": {
        "title": "Choose an action to analyze",
        "Tiger": {
            "numButtons": 3,
            "buttonsName": [
                "open left",
                "listen",
                "open right"
            ]
        },
        "Velocity Regulation": {
            "numButtons": 3,
            "buttonsName": [
                "slow",
                "medium",
                "fast"
            ]
        },
        "next": "variable"
    },
    "variable": {
        "title": "Select a variable name",
        "numButtons": 1,
        "buttonsName": "x1",
        "next": "operator"
    },
    "operator": {
        "title": "Select operator",
        "numButtons": 5,
        "buttonsName": [
            "<",
            "<=",
            "==",
            ">=",
            ">"
        ],
        "next": "state"
    },
    "state": {
        "title": "Select state",
        "Tiger": {
            "numButtons": 2,
            "buttonsName": [
                "tiger left",
                "tiger right"
            ]
        },
        "Velocity Regulation": {
            "numButtons": 3,
            "buttonsName": [
                "low",
                "medium",
                "high"
            ]
        },
        "next": "logic_connector"
    },
    "logic_connector": {
        "title": "Logic connector",
        "numButtons": 3,
        "buttonsName": [
            "I'm done",
            "AND",
            "OR"
        ],
        "next": "variable"
    }
}

export default modalConfig
